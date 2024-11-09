using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.Net.NetworkInformation;
using System.Numerics;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Documents;
using System.Windows.Forms;
using BetterJoy.Collections;
using BetterJoy.Config;
using BetterJoy.Controller;
using BetterJoy.Exceptions;
using Nefarius.ViGEm.Client.Targets.DualShock4;
using Nefarius.ViGEm.Client.Targets.Xbox360;
using WindowsInput.Events;

namespace BetterJoy;

public class Joycon
{
    public enum Button
    {
        DpadDown = 0,
        DpadRight = 1,
        DpadLeft = 2,
        DpadUp = 3,
        SL = 4,
        SR = 5,
        Minus = 6,
        Home = 7,
        Plus = 8,
        Capture = 9,
        LS = 10,
        LB = 11,
        LT = 12,

        // For pro controller
        B = 13,
        A = 14,
        Y = 15,
        X = 16,
        RS = 17,
        RB = 18,
        RT = 19,

        None = 256,
    }

    public enum ControllerType
    {
        JoyconLeft,
        JoyconRight,
        Pro,
        SNES
    }

    public enum DebugType
    {
        None,
        All,
        Comms,
        Threading,
        IMU,
        Rumble,
        Shake,
        Test
    }

    public enum Status : uint
    {
        NotAttached,
        AttachError,
        Errored,
        Dropped,
        Attached,
        IMUDataOk
    }

    public enum BatteryLevel
    {
        Empty,
        Critical,
        Low,
        Medium,
        Full
    }

    public enum Orientation
    {
        None,
        Horizontal,
        Vertical
    }

    public enum Axis
    {
        X,
        Y,
        Z,
        All
    }

    public enum Direction
    {
        Positive,
        Negative,
        Both
    }

    private enum ReceiveError
    {
        None,
        InvalidHandle,
        ReadError,
        InvalidPacket,
        NoData
    }

    private enum ReportMode
    {
        StandardFull = 0x30,
        SimpleHID = 0x3F
    }

    private const int DeviceErroredCode = -100; // custom error

    private const int ReportLength = 49;
    private readonly int _CommandLength;
    private readonly int _MixedComsLength; // when the buffer is used for both read and write to hid

    public readonly ControllerConfig Config;

    private static readonly byte[] LedById = { 0b0001, 0b0011, 0b0111, 0b1111, 0b1001, 0b0101, 0b1101, 0b0110 };

    private readonly short[] _accNeutral = { 0, 0, 0 };
    private readonly short[] _accRaw = { 0, 0, 0 };
    private readonly short[] _accSensiti = { 0, 0, 0 };

    private readonly MadgwickAHRS _AHRS; // for getting filtered Euler angles of rotation; 5ms sampling rate

    private readonly bool[] _buttons = new bool[20];
    private readonly bool[] _buttonsDown = new bool[20];
    private readonly long[] _buttonsDownTimestamp = new long[20];
    private readonly bool[] _buttonsUp = new bool[20];
    private readonly bool[] _buttonsPrev = new bool[20];
    private readonly bool[] _buttonsRemapped = new bool[20];
    private readonly bool[] _buttonsMotion = new bool[20];


    private readonly float[] _curRotation = { 0, 0, 0, 0, 0, 0 }; // Filtered IMU data

    private readonly byte[] _defaultBuf = { 0x0, 0x1, 0x40, 0x40, 0x0, 0x1, 0x40, 0x40 };

    private readonly short[] _gyrNeutral = { 0, 0, 0 };

    private readonly short[] _gyrRaw = { 0, 0, 0 };

    private readonly short[] _gyrSensiti = { 0, 0, 0 };

    private readonly bool _IMUEnabled;
    private readonly Dictionary<int, bool> _mouseToggleBtn = new();

    private readonly float[] _otherStick = { 0, 0 };

    // Values from https://github.com/dekuNukem/Nintendo_Switch_Reverse_Engineering/blob/master/spi_flash_notes.md#6-axis-horizontal-offsets
    private readonly short[] _accProHorOffset = { -688, 0, 4038 };
    private readonly short[] _accLeftHorOffset = { 350, 0, 4081 };
    private readonly short[] _accRightHorOffset = { 350, 0, -4081 };

    private readonly Stopwatch _shakeTimer = Stopwatch.StartNew(); //Setup a timer for measuring shake in milliseconds

    private readonly byte[] _sliderVal = { 0, 0 };

    private readonly ushort[] _stickCal = { 0, 0, 0, 0, 0, 0 };
    private readonly ushort[] _stickPrecal = { 0, 0 };

    private readonly ushort[] _stick2Cal = { 0, 0, 0, 0, 0, 0 };
    private readonly ushort[] _stick2Precal = { 0, 0 };

    private Vector3 _accG = Vector3.Zero;
    public bool ActiveGyro;

    private bool _DumpedCalibration = false;
    private bool _IMUCalibrated = false;
    private bool _SticksCalibrated = false;
    private readonly short[] _activeIMUData = new short[6];
    private readonly ushort[] _activeStick1 = new ushort[6];
    private readonly ushort[] _activeStick2 = new ushort[6];
    private float _activeStick1Deadzone;
    private float _activeStick2Deadzone;
    private float _activeStick1Range;
    private float _activeStick2Range;

    public BatteryLevel Battery = BatteryLevel.Empty;
    public bool Charging = false;

    private float _deadzone;
    private float _deadzone2;
    private float _range;
    private float _range2;

    private bool _doLocalize;

    private MainForm _form;

    private byte _globalCount;
    private Vector3 _gyrG = Vector3.Zero;

    private IntPtr _handle;
    private bool _hasShaked;

    public readonly bool IsThirdParty;
    public readonly bool IsUSB;
    private long _lastDoubleClick = -1;

    public OutputControllerDualShock4 OutDs4;
    public OutputControllerXbox360 OutXbox;
    private readonly object _updateInputLock = new object();

    public int PacketCounter;

    // For UdpServer
    public readonly int PadId;

    public PhysicalAddress PadMacAddress = new([01, 02, 03, 04, 05, 06]);
    public readonly string Path;

    private Thread _receiveReportsThread;
    private Thread _sendCommandsThread;

    private RumbleQueue _rumbles;

    public readonly string SerialNumber;

    public string SerialOrMac;

    private long _shakedTime;

    private Status _state;

    public Status State
    {
        get => _state;
        private set
        {
            if (_state == value)
            {
                return;
            }

            _state = value;
            OnStateChange(new StateChangedEventArgs(value));
        }
    }

    private float[] _stick = { 0, 0 };
    private float[] _stick2 = { 0, 0 };

    private CancellationTokenSource _ctsCommunications;
    public ulong Timestamp { get; private set; }
    public readonly long TimestampCreation;

    private long _timestampActivity = Stopwatch.GetTimestamp();

    public readonly ControllerType Type;

    public EventHandler<StateChangedEventArgs> StateChanged;

    public readonly ConcurrentList<IMUData> CalibrationIMUDatas = new();
    public readonly ConcurrentList<SticksData> CalibrationStickDatas = new();
    private bool _calibrateSticks = false;
    private bool _calibrateIMU = false;

    public readonly ReaderWriterLockSlim HidapiLock = new ReaderWriterLockSlim();

    private Stopwatch _timeSinceReceive = new();
    private RollingAverage _avgReceiveDeltaMs = new(100); // delta is around 10-16ms, so rolling average over 1000-1600ms

    private volatile bool _pauseSendCommands;
    private volatile bool _sendCommandsPaused;

    public Joycon(
        MainForm form,
        IntPtr handle,
        bool imu,
        bool localize,
        string path,
        string serialNum,
        bool isUSB,
        int id,
        ControllerType type,
        bool isThirdParty = false
    )
    {
        _form = form;

        Config = new(_form);
        Config.Update();

        SerialNumber = serialNum;
        SerialOrMac = serialNum;
        _handle = handle;
        _IMUEnabled = imu;
        _doLocalize = localize;
        _rumbles = new RumbleQueue([Config.LowFreq, Config.HighFreq, 0]);
        for (var i = 0; i < _buttonsDownTimestamp.Length; i++)
        {
            _buttonsDownTimestamp[i] = -1;
        }

        _AHRS = new MadgwickAHRS(0.005f, Config.AHRSBeta);

        PadId = id;

        IsUSB = isUSB;
        Type = type;
        IsThirdParty = isThirdParty;
        Path = path;
        _CommandLength = isUSB ? 64 : 49;
        _MixedComsLength = Math.Max(ReportLength, _CommandLength);

        OutXbox = new OutputControllerXbox360();
        OutXbox.FeedbackReceived += ReceiveRumble;

        OutDs4 = new OutputControllerDualShock4();
        OutDs4.FeedbackReceived += Ds4_FeedbackReceived;

        TimestampCreation = new DateTimeOffset(DateTime.UtcNow).ToUnixTimeMilliseconds();
    }

    public bool IsPro => Type is ControllerType.Pro or ControllerType.SNES;
    public bool IsSNES => Type == ControllerType.SNES;
    public bool IsJoycon => Type is ControllerType.JoyconRight or ControllerType.JoyconLeft;
    public bool IsLeft => Type != ControllerType.JoyconRight;
    public bool IsJoined => Other != null && Other != this;
    public bool IsPrimaryGyro => !IsJoined || Config.GyroLeftHanded == IsLeft;

    public bool IsDeviceReady => State > Status.Dropped;
    public bool IsDeviceError => !IsDeviceReady && State != Status.NotAttached;


    public Joycon Other;

    public void SetLEDByPlayerNum(int id)
    {
        if (id >= LedById.Length)
        {
            // No support for any higher than 8 controllers
            id = LedById.Length - 1;
        }

        byte led = LedById[id];

        SetPlayerLED(led);
    }

    public void SetLEDByPadID()
    {
        if (!IsJoined)
        {
            // Set LED to current Pad ID
            SetLEDByPlayerNum(PadId);
        }
        else
        {
            // Set LED to current Joycon Pair
            var lowestPadId = Math.Min(Other.PadId, PadId);
            SetLEDByPlayerNum(lowestPadId);
        }
    }

    public void GetActiveIMUData()
    {
        var activeIMUData = _form.ActiveCaliIMUData(SerialOrMac);

        if (activeIMUData != null)
        {
            Array.Copy(activeIMUData, _activeIMUData, 6);
            _IMUCalibrated = true;
        }
        else
        {
            _IMUCalibrated = false;
        }
    }

    public void GetActiveSticksData()
    {
        _activeStick1Deadzone = Config.DefaultDeadzone;
        _activeStick2Deadzone = Config.DefaultDeadzone;

        _activeStick1Range = Config.DefaultRange;
        _activeStick2Range = Config.DefaultRange;

        var activeSticksData = _form.ActiveCaliSticksData(SerialOrMac);
        if (activeSticksData != null)
        {
            Array.Copy(activeSticksData, _activeStick1, 6);
            Array.Copy(activeSticksData, 6, _activeStick2, 0, 6);
            _SticksCalibrated = true;
        }
        else
        {
            _SticksCalibrated = false;
        }
    }

    public void ReceiveRumble(Xbox360FeedbackReceivedEventArgs e)
    {
        if (!Config.EnableRumble)
        {
            return;
        }

        DebugPrint("Rumble data Received: XInput", DebugType.Rumble);
        SetRumble(Config.LowFreq, Config.HighFreq, Math.Max(e.LargeMotor, e.SmallMotor) / 255f);

        if (IsJoined)
        {
            Other.SetRumble(Config.LowFreq, Config.HighFreq, Math.Max(e.LargeMotor, e.SmallMotor) / 255f);
        }
    }

    public void Ds4_FeedbackReceived(DualShock4FeedbackReceivedEventArgs e)
    {
        if (!Config.EnableRumble)
        {
            return;
        }

        DebugPrint("Rumble data Received: DS4", DebugType.Rumble);
        SetRumble(Config.LowFreq, Config.HighFreq, Math.Max(e.LargeMotor, e.SmallMotor) / 255f);

        if (IsJoined)
        {
            Other.SetRumble(Config.LowFreq, Config.HighFreq, Math.Max(e.LargeMotor, e.SmallMotor) / 255f);
        }
    }

    private void OnStateChange(StateChangedEventArgs e)
    {
        StateChanged?.Invoke(this, e);
    }

    public void DebugPrint(string message, DebugType type)
    {
        if (Config.DebugType == DebugType.None)
        {
            return;
        }

        if (type == DebugType.All || type == Config.DebugType || Config.DebugType == DebugType.All)
        {
            Log(message, Logger.LogLevel.Debug, type);
        }
    }

    public Vector3 GetGyro()
    {
        return _gyrG;
    }

    public Vector3 GetAccel()
    {
        return _accG;
    }

    public bool Reset()
    {
        Log("Resetting connection.");
        return SetHCIState(0x01) > 0;
    }

    public void Attach()
    {
        if (IsDeviceReady)
        {
            return;
        }

        try
        {
            if (_handle == IntPtr.Zero)
            {
                throw new DeviceNullHandleException("reset hidapi");
            }

            // set report mode to simple HID mode (fix SPI read not working when controller is already initialized)
            // do not always send a response so we don't check if there is one
            SetReportMode(ReportMode.SimpleHID);

            // Connect
            if (IsUSB)
            {
                Log("Using USB.");
                GetMAC();
                USBPairing();
                //BTManualPairing();
            }
            else
            {
                Log("Using Bluetooth.");
                GetMAC();
            }

            var ok = DumpCalibrationData();
            if (!ok)
            {
                throw new DeviceComFailedException("reset calibration");
            }

            BlinkHomeLight();
            SetLEDByPlayerNum(PadId);

            SetIMU(_IMUEnabled);
            SetRumble(true);
            SetReportMode(ReportMode.StandardFull);

            State = Status.Attached;

            DebugPrint("Done with init.", DebugType.Comms);
        }
        catch (DeviceComFailedException)
        {
            bool resetSuccess = Reset();
            if (!resetSuccess)
            {
                State = Status.AttachError;
            }
            throw;
        }
        catch
        {
            State = Status.AttachError;
            throw;
        }
    }

    private void GetMAC()
    {
        if (IsUSB)
        {
            Span<byte> buf = stackalloc byte[ReportLength];

            // Get MAC
            if (USBCommandCheck(0x01, buf) < 10)
            {
                // can occur when USB connection isn't closed properly
                throw new DeviceComFailedException("reset mac");
            }

            PadMacAddress = new PhysicalAddress([buf[9], buf[8], buf[7], buf[6], buf[5], buf[4]]);
            SerialOrMac = PadMacAddress.ToString().ToLower();
            return;
        }

        // Serial = MAC address of the controller in bluetooth
        var mac = new byte[6];
        try
        {
            for (var n = 0; n < 6 && n < SerialNumber.Length; n++)
            {
                mac[n] = byte.Parse(SerialNumber.AsSpan(n * 2, 2), NumberStyles.HexNumber);
            }
        }
        // could not parse mac address, ignore
        catch (Exception e)
        {
            Log("Cannot parse MAC address.", e, Logger.LogLevel.Debug);
        }

        PadMacAddress = new PhysicalAddress(mac);
    }

    private void USBPairing()
    {
        // Handshake
        if (USBCommandCheck(0x02) == 0)
        {
            throw new DeviceComFailedException("reset handshake");
        }

        // 3Mbit baud rate
        if (USBCommandCheck(0x03) == 0)
        {
            throw new DeviceComFailedException("reset baud rate");
        }

        // Handshake at new baud rate
        if (USBCommandCheck(0x02) == 0)
        {
            throw new DeviceComFailedException("reset new handshake");
        }

        // Prevent HID timeout
        if (!USBCommand(0x04)) // does not send a response
        {
            throw new DeviceComFailedException("reset new hid timeout");
        }
    }

    private void BTManualPairing()
    {
        Span<byte> buf = stackalloc byte[ReportLength];

        // Bluetooth manual pairing
        byte[] btmac_host = Program.BtMac.GetAddressBytes();

        // send host MAC and acquire Joycon MAC
        SubcommandCheck(0x01, [0x01, btmac_host[5], btmac_host[4], btmac_host[3], btmac_host[2], btmac_host[1], btmac_host[0]], buf);
        SubcommandCheck(0x01, [0x02], buf); // LTKhash
        SubcommandCheck(0x01, [0x03], buf); // save pairing info
    }

    public void SetPlayerLED(byte leds = 0x00)
    {
        SubcommandCheck(0x30, [leds]);
    }

    public void BlinkHomeLight()
    {
        // do not call after initial setup
        if (IsThirdParty || Type == ControllerType.JoyconLeft)
        {
            return;
        }

        const byte intensity = 0x1;

        Span<byte> buf =
        [
            // Global settings
            0x18,
            0x01,

            // Mini cycle 1
            intensity << 4,
            0xFF,
            0xFF,
        ];
        SubcommandCheck(0x38, buf);
    }

    public void SetHomeLight(bool on)
    {
        if (IsThirdParty || Type == ControllerType.JoyconLeft)
        {
            return;
        }

        byte intensity = (byte)(on ? 0x1 : 0x0);
        const byte nbCycles = 0xF; // 0x0 for permanent light

        Span<byte> buf =
        [
            // Global settings
            0x0F, // 0XF = 175ms base duration
            (byte)(intensity << 4 | nbCycles),

            // Mini cycle 1
            // Somehow still used when buf[0] high nibble is set to 0x0
            // Increase the multipliers (like 0xFF instead of 0x11) to increase the duration beyond 2625ms
            (byte)(intensity << 4), // intensity | not used
            0x11, // transition multiplier | duration multiplier, both use the base duration
            0xFF, // not used
        ];
        Subcommand(0x38, buf); // don't wait for response
    }

    private int SetHCIState(byte state)
    {
        return SubcommandCheck(0x06, [state]);
    }

    private void SetIMU(bool enable)
    {
        SubcommandCheck(0x40, [enable ? (byte)0x01 : (byte)0x00]);
    }

    private void SetRumble(bool enable)
    {
        SubcommandCheck(0x48, [enable ? (byte)0x01 : (byte)0x00]);
    }

    private void SetReportMode(ReportMode reportMode, bool checkResponse = true)
    {
        if (checkResponse)
        {
            SubcommandCheck(0x03, [(byte)reportMode]);
            return;
        }
        Subcommand(0x03, [(byte)reportMode]);
    }

    private void BTActivate()
    {
        if (!IsUSB)
        {
            return;
        }

        // Allow device to talk to BT again
        USBCommand(0x05);
        USBCommand(0x06);
    }

    public bool PowerOff()
    {
        if (IsDeviceReady)
        {
            Log("Powering off.");
            if (SetHCIState(0x00) > 0)
            {
                State = Status.Dropped;
                return true;
            }
        }

        return false;
    }

    private void BatteryChanged()
    {
        // battery changed level
        _form.SetBatteryColor(this, Battery);

        if (!IsUSB && !Charging && Battery <= BatteryLevel.Critical)
        {
            var msg = $"Controller {PadId} ({GetControllerName()}) - low battery notification!";
            _form.Tooltip(msg);
        }
    }

    private void ChargingChanged()
    {
        _form.SetCharging(this, Charging);
    }

    public void Detach(bool close = true)
    {
        if (State == Status.NotAttached)
        {
            return;
        }

        WaitCommunicationThreads();
        DisconnectViGEm();
        _rumbles.Clear();

        if (_handle != IntPtr.Zero)
        {
            if (IsDeviceReady)
            {
                //SetIMU(false);
                //SetRumble(false);
                SetReportMode(ReportMode.SimpleHID);
                SetPlayerLED(0);

                // Commented because you need to restart the controller to reconnect in usb again with the following
                //BTActivate();
            }

            if (close)
            {
                HidapiLock.EnterWriteLock();
                try
                {
                    HIDApi.Close(_handle);
                    _handle = IntPtr.Zero;
                }
                finally
                {
                    HidapiLock.ExitWriteLock();
                }
            }
        }

        State = Status.NotAttached;
    }

    public void Drop(bool error = false)
    {
        WaitCommunicationThreads();

        State = error ? Status.Errored : Status.Dropped;
    }

    private void WaitCommunicationThreads()
    {
        _ctsCommunications?.Cancel();
        _receiveReportsThread?.Join();
        _sendCommandsThread?.Join();
        _ctsCommunications?.Dispose();
        _ctsCommunications = null;
    }

    public bool IsViGEmSetup()
    {
        return (!Config.ShowAsXInput || OutXbox.IsConnected()) && (!Config.ShowAsDs4 || OutDs4.IsConnected());
    }

    public void ConnectViGEm()
    {
        if (Config.ShowAsXInput)
        {
            DebugPrint("Connect virtual xbox controller.", DebugType.Comms);
            OutXbox.Connect();
        }

        if (Config.ShowAsDs4)
        {
            DebugPrint("Connect virtual DS4 controller.", DebugType.Comms);
            OutDs4.Connect();
        }
    }

    public void DisconnectViGEm()
    {
        OutXbox.Disconnect();
        OutDs4.Disconnect();
    }

    private void UpdateInput()
    {
        bool lockTaken = false;
        bool otherLockTaken = false;

        if (Type == ControllerType.JoyconLeft)
        {
            Monitor.Enter(_updateInputLock, ref lockTaken); // need with joined joycons
        }

        try
        {
            ref var ds4 = ref OutDs4;
            ref var xbox = ref OutXbox;

            // Update the left joycon virtual controller when joined
            if (!IsLeft && IsJoined)
            {
                Monitor.Enter(Other._updateInputLock, ref otherLockTaken);

                ds4 = ref Other.OutDs4;
                xbox = ref Other.OutXbox;
            }

            ds4.UpdateInput(MapToDualShock4Input(this));
            xbox.UpdateInput(MapToXbox360Input(this));
        }
        // ignore
        catch (Exception e)
        {
            Log("Cannot update input.", e, Logger.LogLevel.Debug);
        }
        finally
        {
            if (lockTaken)
            {
                Monitor.Exit(_updateInputLock);
            }

            if (otherLockTaken)
            {
                Monitor.Exit(Other._updateInputLock);
            }
        }
    }

    // Run from poll thread
    private ReceiveError ReceiveRaw(Span<byte> buf)
    {
        if (_handle == IntPtr.Zero)
        {
            return ReceiveError.InvalidHandle;
        }

        // The controller should report back at 60hz or between 60-120hz for the Pro Controller in USB
        var length = Read(buf, 100);

        if (length < 0)
        {
            return ReceiveError.ReadError;
        }

        if (length == 0)
        {
            return ReceiveError.NoData;
        }

        //DebugPrint($"Received packet {buf[0]:X}", DebugType.Threading);

        byte packetType = buf[0];
        if (packetType != (byte)ReportMode.StandardFull && packetType != (byte)ReportMode.SimpleHID)
        {
            return ReceiveError.InvalidPacket;
        }

        // clear remaining of buffer just to be safe
        if (length < ReportLength)
        {
            buf.Slice(length, ReportLength - length).Clear();
        }

        const int nbPackets = 3;
        ulong deltaPacketsMicroseconds = 0;

        if (packetType == (byte)ReportMode.StandardFull)
        {
            // Determine the IMU timestamp with a rolling average instead of relying on the unreliable packet's timestamp
            // more detailed explanations on why : https://github.com/torvalds/linux/blob/52b1853b080a082ec3749c3a9577f6c71b1d4a90/drivers/hid/hid-nintendo.c#L1115
            if (_timeSinceReceive.IsRunning)
            {
                var deltaReceiveMs = _timeSinceReceive.ElapsedMilliseconds;
                _avgReceiveDeltaMs.AddValue((int)deltaReceiveMs);
            }
            _timeSinceReceive.Restart();

            var deltaPacketsMs = _avgReceiveDeltaMs.GetAverage() / nbPackets;
            deltaPacketsMicroseconds = (ulong)(deltaPacketsMs * 1000);

            _AHRS.SamplePeriod = deltaPacketsMs / 1000;
        }

        // Process packets as soon as they come
        for (var n = 0; n < nbPackets; n++)
        {
            bool updateIMU = ExtractIMUValues(buf, n);

            if (n == 0)
            {
                ProcessButtonsAndStick(buf);
                HandleMotionControls();
                DoThingsWithButtons();
                GetBatteryInfos(buf);
            }

            if (!updateIMU)
            {
                break;
            }

            Timestamp += deltaPacketsMicroseconds;
            PacketCounter++;

            if (IsPrimaryGyro)
            {
                Program.Server?.NewReportIncoming(this);
            }
        }

        UpdateInput();

        //DebugPrint($"Bytes read: {length:D}. Elapsed: {deltaReceiveMs}ms AVG: {_avgReceiveDeltaMs.GetAverage()}ms", DebugType.Threading);

        return ReceiveError.None;
    }

    private Button GetButtonForMotion(Button p1Button, Button p2Button)
    {
        // PadId 0 and 1 are for P1, PadId 2 and 3 are for P2
        bool isP1 = PadId < 2;
        return isP1 ? p1Button : p2Button;
    }

    private enum SequentialPressState
    {
        Idle,
        FirstPress,
        BetweenFirstAndSecond,
        SecondPress,
        Cooldown
    }

    public enum PressType
    {
        Single,
        Continuous,
        Double,
    }

    // Existing variables (some have been updated)

    // Enabled flags
    private bool _leftGyroEnabled = true;
    private bool _leftGyroZEnabled = false;
    private bool _leftGyroZPlusEnabled = false;
    private bool _leftGyroZMinusEnabled = false;
    private bool _leftAccelEnabled = false;
    private bool _leftAccelXEnabled = false;

    private bool _rightGyroEnabled = true;
    private bool _rightGyroZEnabled = false;
    private bool _rightGyroZPlusEnabled = false;
    private bool _rightGyroZMinusEnabled = false;
    private bool _rightAccelEnabled = false;
    private bool _rightAccelXEnabled = false;

    // Combo enabled flags
    private bool _leftGyroComboEnabled = false;
    private bool _leftGyroZComboEnabled = false;
    private bool _leftGyroZPlusComboEnabled = false;
    private bool _leftGyroZMinusComboEnabled = false;
    private bool _leftAccelComboEnabled = false;
    private bool _leftAccelXComboEnabled = false;

    private bool _rightGyroComboEnabled = false;
    private bool _rightGyroZComboEnabled = false;
    private bool _rightGyroZPlusComboEnabled = false;
    private bool _rightGyroZMinusComboEnabled = false;
    private bool _rightAccelComboEnabled = false;
    private bool _rightAccelXComboEnabled = false;

    // Heavy enabled flags
    private bool _leftGyroHeavyEnabled = false;
    private bool _leftGyroZHeavyEnabled = false;
    private bool _leftGyroZPlusHeavyEnabled = false;
    private bool _leftGyroZMinusHeavyEnabled = false;
    private bool _leftAccelHeavyEnabled = false;
    private bool _leftAccelXHeavyEnabled = false;

    private bool _rightGyroHeavyEnabled = false;
    private bool _rightGyroZHeavyEnabled = false;
    private bool _rightGyroZPlusHeavyEnabled = false;
    private bool _rightGyroZMinusHeavyEnabled = false;
    private bool _rightAccelHeavyEnabled = false;
    private bool _rightAccelXHeavyEnabled = false;

    // Buttons
    private Button _leftGyroButton = Button.A;
    private Button _leftGyroZButton = Button.A;
    private Button _leftGyroZPlusButton = Button.A;
    private Button _leftGyroZMinusButton = Button.A;
    private Button _leftAccelButton = Button.A;
    private Button _leftAccelXButton = Button.A;

    private Button _rightGyroButton = Button.B;
    private Button _rightGyroZButton = Button.B;
    private Button _rightGyroZPlusButton = Button.B;
    private Button _rightGyroZMinusButton = Button.B;
    private Button _rightAccelButton = Button.B;
    private Button _rightAccelXButton = Button.B;

    private Button _leftGyroButtonP1 = Button.A;
    private Button _leftGyroZButtonP1 = Button.A;
    private Button _leftGyroZPlusButtonP1 = Button.A;
    private Button _leftGyroZMinusButtonP1 = Button.A;
    private Button _leftAccelButtonP1 = Button.A;
    private Button _leftAccelXButtonP1 = Button.A;
    private Button _rightGyroButtonP1 = Button.B;
    private Button _rightGyroZButtonP1 = Button.B;
    private Button _rightGyroZPlusButtonP1 = Button.B;
    private Button _rightGyroZMinusButtonP1 = Button.B;
    private Button _rightAccelButtonP1 = Button.B;
    private Button _rightAccelXButtonP1 = Button.B;

    private Button _leftGyroButtonP2 = Button.Minus;
    private Button _leftGyroZButtonP2 = Button.Minus;
    private Button _leftGyroZPlusButtonP2 = Button.Minus;
    private Button _leftGyroZMinusButtonP2 = Button.Minus;
    private Button _leftAccelButtonP2 = Button.Minus;
    private Button _leftAccelXButtonP2 = Button.Minus;
    private Button _rightGyroButtonP2 = Button.Plus;
    private Button _rightGyroZButtonP2 = Button.Plus;
    private Button _rightGyroZPlusButtonP2 = Button.Plus;
    private Button _rightGyroZMinusButtonP2 = Button.Plus;
    private Button _rightAccelButtonP2 = Button.Plus;
    private Button _rightAccelXButtonP2 = Button.Plus;

    // Secondary buttons
    private Button? _leftGyroSecondaryButton = null;
    private Button? _leftGyroZSecondaryButton = null;
    private Button? _leftGyroZPlusSecondaryButton = null;
    private Button? _leftGyroZMinusSecondaryButton = null;
    private Button? _leftAccelSecondaryButton = null;
    private Button? _leftAccelXSecondaryButton = null;

    private Button? _rightGyroSecondaryButton = null;
    private Button? _rightGyroZSecondaryButton = null;
    private Button? _rightGyroZPlusSecondaryButton = null;
    private Button? _rightGyroZMinusSecondaryButton = null;
    private Button? _rightAccelSecondaryButton = null;
    private Button? _rightAccelXSecondaryButton = null;

    // Secondary button delays
    private long _leftGyroSecondaryButtonDelay = 0;
    private long _leftGyroZSecondaryButtonDelay = 0;
    private long _leftGyroZPlusSecondaryButtonDelay = 0;
    private long _leftGyroZMinusSecondaryButtonDelay = 0;
    private long _leftAccelSecondaryButtonDelay = 0;
    private long _leftAccelXSecondaryButtonDelay = 0;

    private long _rightGyroSecondaryButtonDelay = 0;
    private long _rightGyroZSecondaryButtonDelay = 0;
    private long _rightGyroZPlusSecondaryButtonDelay = 0;
    private long _rightGyroZMinusSecondaryButtonDelay = 0;
    private long _rightAccelSecondaryButtonDelay = 0;
    private long _rightAccelXSecondaryButtonDelay = 0;

    // Thresholds
    private float _leftGyroThreshold = 100f;
    private float _leftGyroZThreshold = 100f;
    private float _leftGyroZPlusThreshold = 200f;
    private float _leftGyroZMinusThreshold = 200f;
    private float _leftAccelThreshold = 9991.0f;
    private float _leftAccelXThreshold = 9991.0f;

    private float _rightGyroThreshold = 100f;
    private float _rightGyroZThreshold = 100f;
    private float _rightGyroZPlusThreshold = 200f;
    private float _rightGyroZMinusThreshold = 200f;
    private float _rightAccelThreshold = 9991.0f;
    private float _rightAccelXThreshold = 9991.0f;

    // Cooldown durations
    private long _leftGyroCooldownDuration = 300;
    private long _leftGyroZCooldownDuration = 300;
    private long _leftGyroZPlusCooldownDuration = 300;
    private long _leftGyroZMinusCooldownDuration = 300;
    private long _leftAccelCooldownDuration = 0;
    private long _leftAccelXCooldownDuration = 0;

    private long _rightGyroCooldownDuration = 100;
    private long _rightGyroZCooldownDuration = 100;
    private long _rightGyroZPlusCooldownDuration = 100;
    private long _rightGyroZMinusCooldownDuration = 100;
    private long _rightAccelCooldownDuration = 100;
    private long _rightAccelXCooldownDuration = 100;

    // External cooldown durations
    private long _leftGyroExternalCooldownDuration = 100;
    private long _leftGyroZExternalCooldownDuration = 100;
    private long _leftGyroZPlusExternalCooldownDuration = 100;
    private long _leftGyroZMinusExternalCooldownDuration = 100;
    private long _leftAccelExternalCooldownDuration = 100;
    private long _leftAccelXExternalCooldownDuration = 100;

    private long _rightGyroExternalCooldownDuration = 100;
    private long _rightGyroZExternalCooldownDuration = 100;
    private long _rightGyroZPlusExternalCooldownDuration = 100;
    private long _rightGyroZMinusExternalCooldownDuration = 100;
    private long _rightAccelExternalCooldownDuration = 100;
    private long _rightAccelXExternalCooldownDuration = 100;

    // Press durations
    private long _leftGyroPressDuration = 100;
    private long _leftGyroZPressDuration = 100;
    private long _leftGyroZPlusPressDuration = 100;
    private long _leftGyroZMinusPressDuration = 100;
    private long _leftAccelPressDuration = 100;
    private long _leftAccelXPressDuration = 100;

    private long _rightGyroPressDuration = 100;
    private long _rightGyroZPressDuration = 100;
    private long _rightGyroZPlusPressDuration = 100;
    private long _rightGyroZMinusPressDuration = 100;
    private long _rightAccelPressDuration = 100;
    private long _rightAccelXPressDuration = 100;

    // Press types
    private PressType _leftGyroPressType = PressType.Single;
    private PressType _leftGyroZPressType = PressType.Single;
    private PressType _leftGyroZPlusPressType = PressType.Single;
    private PressType _leftGyroZMinusPressType = PressType.Single;
    private PressType _leftAccelPressType = PressType.Single;
    private PressType _leftAccelXPressType = PressType.Single;

    private PressType _rightGyroPressType = PressType.Single;
    private PressType _rightGyroZPressType = PressType.Single;
    private PressType _rightGyroZPlusPressType = PressType.Single;
    private PressType _rightGyroZMinusPressType = PressType.Single;
    private PressType _rightAccelPressType = PressType.Single;
    private PressType _rightAccelXPressType = PressType.Single;

    // Minimum breach times
    private long _leftGyroMinBreachTime = 0;
    private long _leftGyroZMinBreachTime = 0;
    private long _leftGyroZPlusMinBreachTime = 0;
    private long _leftGyroZMinusMinBreachTime = 0;
    private long _leftAccelMinBreachTime = 0;
    private long _leftAccelXMinBreachTime = 0;

    private long _rightGyroMinBreachTime = 0;
    private long _rightGyroZMinBreachTime = 0;
    private long _rightGyroZPlusMinBreachTime = 0;
    private long _rightGyroZMinusMinBreachTime = 0;
    private long _rightAccelMinBreachTime = 0;
    private long _rightAccelXMinBreachTime = 0;

    // Combo buttons
    private Button _leftGyroComboButton = Button.None;
    private Button _leftGyroZComboButton = Button.None;
    private Button _leftGyroZPlusComboButton = Button.None;
    private Button _leftGyroZMinusComboButton = Button.None;
    private Button _leftAccelComboButton = Button.None;
    private Button _leftAccelXComboButton = Button.None;

    private Button _rightGyroComboButton = Button.None;
    private Button _rightGyroZComboButton = Button.None;
    private Button _rightGyroZPlusComboButton = Button.None;
    private Button _rightGyroZMinusComboButton = Button.None;
    private Button _rightAccelComboButton = Button.None;
    private Button _rightAccelXComboButton = Button.None;

    // Combo pressed flags
    private bool _leftGyroComboPressed = false, _leftGyroZComboPressed = false, _leftGyroZPlusComboPressed = false, _leftGyroZMinusComboPressed = false, _leftAccelComboPressed = false, _leftAccelXComboPressed = false,
                 _rightGyroComboPressed = false, _rightGyroZComboPressed = false, _rightGyroZPlusComboPressed = false, _rightGyroZMinusComboPressed = false, _rightAccelComboPressed = false, _rightAccelXComboPressed = false;

    // Combo start times
    private long _leftGyroComboStartTime = 0;
    private long _leftGyroZComboStartTime = 0;
    private long _leftGyroZPlusComboStartTime = 0;
    private long _leftGyroZMinusComboStartTime = 0;
    private long _leftAccelComboStartTime = 0;
    private long _leftAccelXComboStartTime = 0;

    private long _rightGyroComboStartTime = 0;
    private long _rightGyroZComboStartTime = 0;
    private long _rightGyroZPlusComboStartTime = 0;
    private long _rightGyroZMinusComboStartTime = 0;
    private long _rightAccelComboStartTime = 0;
    private long _rightAccelXComboStartTime = 0;

    // Opposite threshold breached flags
    private bool _leftGyroOppositeThresholdBreached = false, _leftGyroZOppositeThresholdBreached = false, _leftGyroZPlusOppositeThresholdBreached = false, _leftGyroZMinusOppositeThresholdBreached = false, _leftAccelOppositeThresholdBreached = false, _leftAccelXOppositeThresholdBreached = false,
                _rightGyroOppositeThresholdBreached = false, _rightGyroZOppositeThresholdBreached = false, _rightGyroZPlusOppositeThresholdBreached = false, _rightGyroZMinusOppositeThresholdBreached = false, _rightAccelOppositeThresholdBreached = false, _rightAccelXOppositeThresholdBreached = false;

    // Heavy press variables
    private float _leftGyroHeavyThreshold = 0f;
    private float _leftGyroZHeavyThreshold = 0f;
    private float _leftGyroZPlusHeavyThreshold = 0f;
    private float _leftGyroZMinusHeavyThreshold = 0f;
    private float _leftAccelHeavyThreshold = 0f;
    private float _leftAccelXHeavyThreshold = 0f;

    private float _rightGyroHeavyThreshold = 0f;
    private float _rightGyroZHeavyThreshold = 0f;
    private float _rightGyroZPlusHeavyThreshold = 0f;
    private float _rightGyroZMinusHeavyThreshold = 0f;
    private float _rightAccelHeavyThreshold = 0f;
    private float _rightAccelXHeavyThreshold = 0f;

    // Heavy buttons
    private Button _leftGyroHeavyButton = Button.None;
    private Button _leftGyroZHeavyButton = Button.None;
    private Button _leftGyroZPlusHeavyButton = Button.None;
    private Button _leftGyroZMinusHeavyButton = Button.None;
    private Button _leftAccelHeavyButton = Button.None;
    private Button _leftAccelXHeavyButton = Button.None;

    private Button _rightGyroHeavyButton = Button.None;
    private Button _rightGyroZHeavyButton = Button.None;
    private Button _rightGyroZPlusHeavyButton = Button.None;
    private Button _rightGyroZMinusHeavyButton = Button.None;
    private Button _rightAccelHeavyButton = Button.None;
    private Button _rightAccelXHeavyButton = Button.None;

    // Heavy start times
    private long _leftGyroHeavyStartTime = 0, _leftGyroZHeavyStartTime = 0, _leftGyroZPlusHeavyStartTime = 0, _leftGyroZMinusHeavyStartTime = 0, _leftAccelHeavyStartTime = 0, _leftAccelXHeavyStartTime = 0,
              _rightGyroHeavyStartTime = 0, _rightGyroZHeavyStartTime = 0, _rightGyroZPlusHeavyStartTime = 0, _rightGyroZMinusHeavyStartTime = 0, _rightAccelHeavyStartTime = 0, _rightAccelXHeavyStartTime = 0;

    // Heavy pressed flags
    private bool _leftGyroHeavyPressed = false, _leftGyroZHeavyPressed = false, _leftGyroZPlusHeavyPressed = false, _leftGyroZMinusHeavyPressed = false, _leftAccelHeavyPressed = false, _leftAccelXHeavyPressed = false,
              _rightGyroHeavyPressed = false, _rightGyroZHeavyPressed = false, _rightGyroZPlusHeavyPressed = false, _rightGyroZMinusHeavyPressed = false, _rightAccelHeavyPressed = false, _rightAccelXHeavyPressed = false;

    // Pressed flags
    private bool _leftGyroPressed = false, _leftGyroZPressed = false, _leftGyroZPlusPressed = false, _leftGyroZMinusPressed = false, _leftAccelPressed = false, _leftAccelXPressed = false,
              _rightGyroPressed = false, _rightGyroZPressed = false, _rightGyroZPlusPressed = false, _rightGyroZMinusPressed = false, _rightAccelPressed = false, _rightAccelXPressed = false;

    // Last press times
    private long _lastLeftGyroTime = 0, _lastLeftGyroZTime = 0, _lastLeftGyroZPlusTime = 0, _lastLeftGyroZMinusTime = 0, _lastLeftAccelTime = 0, _lastLeftAccelXTime = 0,
             _lastRightGyroTime = 0, _lastRightGyroZTime = 0, _lastRightGyroZPlusTime = 0, _lastRightGyroZMinusTime = 0, _lastRightAccelTime = 0, _lastRightAccelXTime = 0;

    // Last motion times
    private long _lastLeftGyroMotionTime = 0, _lastLeftGyroZMotionTime = 0, _lastLeftGyroZPlusMotionTime = 0, _lastLeftGyroZMinusMotionTime = 0, _lastLeftAccelMotionTime = 0, _lastLeftAccelXMotionTime = 0,
             _lastRightGyroMotionTime = 0, _lastRightGyroZMotionTime = 0, _lastRightGyroZPlusMotionTime = 0, _lastRightGyroZMinusMotionTime = 0, _lastRightAccelMotionTime = 0, _lastRightAccelXMotionTime = 0;

    // Second press flags
    private bool _leftGyroSecondPress = false, _leftGyroZSecondPress = false, _leftGyroZPlusSecondPress = false, _leftGyroZMinusSecondPress = false, _leftAccelSecondPress = false, _leftAccelXSecondPress = false,
              _rightGyroSecondPress = false, _rightGyroZSecondPress = false, _rightGyroZPlusSecondPress = false, _rightGyroZMinusSecondPress = false, _rightAccelSecondPress = false, _rightAccelXSecondPress = false;

    // Sequential press states
    private SequentialPressState _leftGyroSequentialPressState = SequentialPressState.Idle, _leftGyroZSequentialPressState = SequentialPressState.Idle, _leftGyroZPlusSequentialPressState = SequentialPressState.Idle, _leftGyroZMinusSequentialPressState = SequentialPressState.Idle, _leftAccelSequentialPressState = SequentialPressState.Idle, _leftAccelXSequentialPressState = SequentialPressState.Idle,
                                _rightGyroSequentialPressState = SequentialPressState.Idle, _rightGyroZSequentialPressState = SequentialPressState.Idle, _rightGyroZPlusSequentialPressState = SequentialPressState.Idle, _rightGyroZMinusSequentialPressState = SequentialPressState.Idle, _rightAccelSequentialPressState = SequentialPressState.Idle, _rightAccelXSequentialPressState = SequentialPressState.Idle;

    // External cooldown times
    private long _lastLeftGyroExternalCooldownTime = 0, _lastLeftGyroZExternalCooldownTime = 0, _lastLeftGyroZPlusExternalCooldownTime = 0, _lastLeftGyroZMinusExternalCooldownTime = 0, _lastLeftAccelExternalCooldownTime = 0, _lastLeftAccelXExternalCooldownTime = 0,
             _lastRightGyroExternalCooldownTime = 0, _lastRightGyroZExternalCooldownTime = 0, _lastRightGyroZPlusExternalCooldownTime = 0, _lastRightGyroZMinusExternalCooldownTime = 0, _lastRightAccelExternalCooldownTime = 0, _lastRightAccelXExternalCooldownTime = 0;

    // Breach start times
    private long _leftGyroBreachStartTime = 0, _leftGyroZBreachStartTime = 0, _leftGyroZPlusBreachStartTime = 0, _leftGyroZMinusBreachStartTime = 0, _leftAccelBreachStartTime = 0, _leftAccelXBreachStartTime = 0,
             _rightGyroBreachStartTime = 0, _rightGyroZBreachStartTime = 0, _rightGyroZPlusBreachStartTime = 0, _rightGyroZMinusBreachStartTime = 0, _rightAccelBreachStartTime = 0, _rightAccelXBreachStartTime = 0;

    // Combo window
    private long _comboWindow = 70; // milliseconds

    // Heavy press window
    private long _heavyPressWindow = 70; // milliseconds

    // Methods to set enabled flags
    public void SetGyroEnabled(bool isLeft, bool enabled)
    {
        if (isLeft)
            _leftGyroEnabled = enabled;
        else
            _rightGyroEnabled = enabled;
    }

    public void SetAccelEnabled(bool isLeft, bool enabled)
    {
        if (isLeft)
            _leftAccelEnabled = enabled;
        else
            _rightAccelEnabled = enabled;
    }

    public void SetGyroZEnabled(bool isLeft, bool enabled)
    {
        if (isLeft)
            _leftGyroZEnabled = enabled;
        else
            _rightGyroZEnabled = enabled;
    }

    public void SetAccelXEnabled(bool isLeft, bool enabled)
    {
        if (isLeft)
            _leftAccelXEnabled = enabled;
        else
            _rightAccelXEnabled = enabled;
    }

    // New methods to set gyroZPlus and gyroZMinus enabled flags
    public void SetGyroZPlusEnabled(bool isLeft, bool enabled)
    {
        if (isLeft)
            _leftGyroZPlusEnabled = enabled;
        else
            _rightGyroZPlusEnabled = enabled;
    }

    public void SetGyroZMinusEnabled(bool isLeft, bool enabled)
    {
        if (isLeft)
            _leftGyroZMinusEnabled = enabled;
        else
            _rightGyroZMinusEnabled = enabled;
    }

    private void HandleMotionControls()
    {
        long currentTime = DateTimeOffset.Now.ToUnixTimeMilliseconds();

        // Handle the current Joy-Con
        HandleJoyconMotion(this, currentTime);

        // Handle the other Joy-Con only if it exists
        if (Other != null)
        {
            HandleJoyconMotion(Other, currentTime);
        }
    }

    private void HandleJoyconMotion(Joycon joycon, long currentTime)
    {
        if (joycon == null)
        {
            return;
        }

        // Get accelerometer and gyroscope data
        Vector3 accel = joycon.GetAccel();
        Vector3 gyro = joycon.GetGyro();

        // Process each motion control separately
        ProcessMotionControl(joycon, currentTime, Axis.All, Direction.Both, gyro, accel);
        ProcessMotionControl(joycon, currentTime, Axis.Z, Direction.Both, gyro, accel);
        ProcessMotionControl(joycon, currentTime, Axis.Z, Direction.Positive, gyro, accel);
        ProcessMotionControl(joycon, currentTime, Axis.Z, Direction.Negative, gyro, accel);
        ProcessMotionControl(joycon, currentTime, Axis.X, Direction.Both, gyro, accel);
    }

    // New method to process individual motion controls
    private void ProcessMotionControl(Joycon joycon, long currentTime, Axis axis, Direction direction, Vector3 gyro, Vector3 accel)
    {
        bool isLeft = joycon.IsLeft;

        // Determine which control we're processing
        bool gyroEnabled = false;
        bool accelEnabled = false;
        float gyroThreshold = 0f;
        float accelThreshold = 0f;
        float gyroHeavyThreshold = 0f;
        float accelHeavyThreshold = 0f;
        long gyroCooldownDuration = 0;
        long accelCooldownDuration = 0;
        long gyroExternalCooldownDuration = 0;
        long accelExternalCooldownDuration = 0;
        long gyroPressDuration = 0;
        long accelPressDuration = 0;
        long gyroMinBreachTime = 0;
        long accelMinBreachTime = 0;
        Button gyroButton = Button.None;
        Button accelButton = Button.None;
        Button gyroComboButton = Button.None;
        Button accelComboButton = Button.None;
        Button gyroHeavyButton = Button.None;
        Button accelHeavyButton = Button.None;
        bool gyroComboEnabled = false;
        bool accelComboEnabled = false;
        bool gyroHeavyEnabled = false;
        bool accelHeavyEnabled = false;
        Button? gyroSecondaryButton = null;
        Button? accelSecondaryButton = null;
        long gyroSecondaryButtonDelay = 0;
        long accelSecondaryButtonDelay = 0;
        PressType gyroPressType = PressType.Single;
        PressType accelPressType = PressType.Single;

        // References to shared variables
        ref bool gyroPressed = ref _leftGyroPressed;
        ref bool accelPressed = ref _leftAccelPressed;
        ref long lastGyroTime = ref _lastLeftGyroTime;
        ref long lastAccelTime = ref _lastLeftAccelTime;
        ref long lastGyroMotionTime = ref _lastLeftGyroMotionTime;
        ref long lastAccelMotionTime = ref _lastLeftAccelMotionTime;
        ref bool gyroComboPressed = ref _leftGyroComboPressed;
        ref bool accelComboPressed = ref _leftAccelComboPressed;
        ref long gyroComboStartTime = ref _leftGyroComboStartTime;
        ref long accelComboStartTime = ref _leftAccelComboStartTime;
        ref bool gyroOppositeThresholdBreached = ref _leftGyroOppositeThresholdBreached;
        ref bool accelOppositeThresholdBreached = ref _leftAccelOppositeThresholdBreached;
        ref bool gyroHeavyPressed = ref _leftGyroHeavyPressed;
        ref bool accelHeavyPressed = ref _leftAccelHeavyPressed;
        ref long gyroHeavyStartTime = ref _leftGyroHeavyStartTime;
        ref long accelHeavyStartTime = ref _leftAccelHeavyStartTime;
        ref bool gyroSecondPress = ref _leftGyroSecondPress;
        ref bool accelSecondPress = ref _leftAccelSecondPress;
        ref SequentialPressState gyroSequentialPressState = ref _leftGyroSequentialPressState;
        ref SequentialPressState accelSequentialPressState = ref _leftAccelSequentialPressState;
        ref long lastGyroExternalCooldownTime = ref _lastLeftGyroExternalCooldownTime;
        ref long lastAccelExternalCooldownTime = ref _lastLeftAccelExternalCooldownTime;
        ref long gyroBreachStartTime = ref _leftGyroBreachStartTime;
        ref long accelBreachStartTime = ref _leftAccelBreachStartTime;

        // Set up variables based on axis, direction, and side
        if (isLeft)
        {
            if (axis == Axis.All && direction == Direction.Both)
            {
                // Existing code for leftGyro and leftAccel
                gyroEnabled = _leftGyroEnabled;
                accelEnabled = _leftAccelEnabled;
                gyroThreshold = _leftGyroThreshold;
                accelThreshold = _leftAccelThreshold;
                gyroHeavyThreshold = _leftGyroHeavyThreshold;
                accelHeavyThreshold = _leftAccelHeavyThreshold;
                gyroCooldownDuration = _leftGyroCooldownDuration;
                accelCooldownDuration = _leftAccelCooldownDuration;
                gyroExternalCooldownDuration = _leftGyroExternalCooldownDuration;
                accelExternalCooldownDuration = _leftAccelExternalCooldownDuration;
                gyroPressDuration = _leftGyroPressDuration;
                accelPressDuration = _leftAccelPressDuration;
                gyroMinBreachTime = _leftGyroMinBreachTime;
                accelMinBreachTime = _leftAccelMinBreachTime;
                gyroButton = GetButtonForMotion(_leftGyroButtonP1, _leftGyroButtonP2);
                accelButton = GetButtonForMotion(_leftAccelButtonP1, _leftAccelButtonP2);
                gyroComboButton = _leftGyroComboButton;
                accelComboButton = _leftAccelComboButton;
                gyroHeavyButton = _leftGyroHeavyButton;
                accelHeavyButton = _leftAccelHeavyButton;
                gyroComboEnabled = _leftGyroComboEnabled;
                accelComboEnabled = _leftAccelComboEnabled;
                gyroHeavyEnabled = _leftGyroHeavyEnabled;
                accelHeavyEnabled = _leftAccelHeavyEnabled;
                gyroSecondaryButton = _leftGyroSecondaryButton;
                accelSecondaryButton = _leftAccelSecondaryButton;
                gyroSecondaryButtonDelay = _leftGyroSecondaryButtonDelay;
                accelSecondaryButtonDelay = _leftAccelSecondaryButtonDelay;
                gyroPressType = _leftGyroPressType;
                accelPressType = _leftAccelPressType;
                gyroPressed = ref _leftGyroPressed;
                accelPressed = ref _leftAccelPressed;
                lastGyroTime = ref _lastLeftGyroTime;
                lastAccelTime = ref _lastLeftAccelTime;
                lastGyroMotionTime = ref _lastLeftGyroMotionTime;
                lastAccelMotionTime = ref _lastLeftAccelMotionTime;
                gyroComboPressed = ref _leftGyroComboPressed;
                accelComboPressed = ref _leftAccelComboPressed;
                gyroComboStartTime = ref _leftGyroComboStartTime;
                accelComboStartTime = ref _leftAccelComboStartTime;
                gyroOppositeThresholdBreached = ref _leftGyroOppositeThresholdBreached;
                accelOppositeThresholdBreached = ref _leftAccelOppositeThresholdBreached;
                gyroHeavyPressed = ref _leftGyroHeavyPressed;
                accelHeavyPressed = ref _leftAccelHeavyPressed;
                gyroHeavyStartTime = ref _leftGyroHeavyStartTime;
                accelHeavyStartTime = ref _leftAccelHeavyStartTime;
                gyroSecondPress = ref _leftGyroSecondPress;
                accelSecondPress = ref _leftAccelSecondPress;
                gyroSequentialPressState = ref _leftGyroSequentialPressState;
                accelSequentialPressState = ref _leftAccelSequentialPressState;
                lastGyroExternalCooldownTime = ref _lastLeftGyroExternalCooldownTime;
                lastAccelExternalCooldownTime = ref _lastLeftAccelExternalCooldownTime;
                gyroBreachStartTime = ref _leftGyroBreachStartTime;
                accelBreachStartTime = ref _leftAccelBreachStartTime;
            }
            else if (axis == Axis.Z && direction == Direction.Both)
            {
                // Existing code for leftGyroZ
                gyroEnabled = _leftGyroZEnabled;
                gyroThreshold = _leftGyroZThreshold;
                gyroHeavyThreshold = _leftGyroZHeavyThreshold;
                gyroCooldownDuration = _leftGyroZCooldownDuration;
                gyroExternalCooldownDuration = _leftGyroZExternalCooldownDuration;
                gyroPressDuration = _leftGyroZPressDuration;
                gyroMinBreachTime = _leftGyroZMinBreachTime;
                gyroButton = GetButtonForMotion(_leftGyroZButtonP1, _leftGyroZButtonP2);
                gyroComboButton = _leftGyroZComboButton;
                gyroHeavyButton = _leftGyroZHeavyButton;
                gyroComboEnabled = _leftGyroZComboEnabled;
                gyroHeavyEnabled = _leftGyroZHeavyEnabled;
                gyroSecondaryButton = _leftGyroZSecondaryButton;
                gyroSecondaryButtonDelay = _leftGyroZSecondaryButtonDelay;
                gyroPressType = _leftGyroZPressType;
                gyroPressed = ref _leftGyroZPressed;
                lastGyroTime = ref _lastLeftGyroZTime;
                lastGyroMotionTime = ref _lastLeftGyroZMotionTime;
                gyroComboPressed = ref _leftGyroZComboPressed;
                gyroComboStartTime = ref _leftGyroZComboStartTime;
                gyroOppositeThresholdBreached = ref _leftGyroZOppositeThresholdBreached;
                gyroHeavyPressed = ref _leftGyroZHeavyPressed;
                gyroHeavyStartTime = ref _leftGyroZHeavyStartTime;
                gyroSecondPress = ref _leftGyroZSecondPress;
                gyroSequentialPressState = ref _leftGyroZSequentialPressState;
                lastGyroExternalCooldownTime = ref _lastLeftGyroZExternalCooldownTime;
                gyroBreachStartTime = ref _leftGyroZBreachStartTime;
            }
            else if (axis == Axis.Z && direction == Direction.Positive)
            {
                gyroEnabled = _leftGyroZPlusEnabled;
                gyroThreshold = _leftGyroZPlusThreshold;
                gyroHeavyThreshold = _leftGyroZPlusHeavyThreshold;
                gyroCooldownDuration = _leftGyroZPlusCooldownDuration;
                gyroExternalCooldownDuration = _leftGyroZPlusExternalCooldownDuration;
                gyroPressDuration = _leftGyroZPlusPressDuration;
                gyroMinBreachTime = _leftGyroZPlusMinBreachTime;
                gyroButton = GetButtonForMotion(_leftGyroZPlusButtonP1, _leftGyroZPlusButtonP2);
                gyroComboButton = _leftGyroZPlusComboButton;
                gyroHeavyButton = _leftGyroZPlusHeavyButton;
                gyroComboEnabled = _leftGyroZPlusComboEnabled;
                gyroHeavyEnabled = _leftGyroZPlusHeavyEnabled;
                gyroSecondaryButton = _leftGyroZPlusSecondaryButton;
                gyroSecondaryButtonDelay = _leftGyroZPlusSecondaryButtonDelay;
                gyroPressType = _leftGyroZPlusPressType;
                gyroPressed = ref _leftGyroZPlusPressed;
                lastGyroTime = ref _lastLeftGyroZPlusTime;
                lastGyroMotionTime = ref _lastLeftGyroZPlusMotionTime;
                gyroComboPressed = ref _leftGyroZPlusComboPressed;
                gyroComboStartTime = ref _leftGyroZPlusComboStartTime;
                gyroOppositeThresholdBreached = ref _leftGyroZPlusOppositeThresholdBreached;
                gyroHeavyPressed = ref _leftGyroZPlusHeavyPressed;
                gyroHeavyStartTime = ref _leftGyroZPlusHeavyStartTime;
                gyroSecondPress = ref _leftGyroZPlusSecondPress;
                gyroSequentialPressState = ref _leftGyroZPlusSequentialPressState;
                lastGyroExternalCooldownTime = ref _lastLeftGyroZPlusExternalCooldownTime;
                gyroBreachStartTime = ref _leftGyroZPlusBreachStartTime;
            }
            else if (axis == Axis.Z && direction == Direction.Negative)
            {
                gyroEnabled = _leftGyroZMinusEnabled;
                gyroThreshold = _leftGyroZMinusThreshold;
                gyroHeavyThreshold = _leftGyroZMinusHeavyThreshold;
                gyroCooldownDuration = _leftGyroZMinusCooldownDuration;
                gyroExternalCooldownDuration = _leftGyroZMinusExternalCooldownDuration;
                gyroPressDuration = _leftGyroZMinusPressDuration;
                gyroMinBreachTime = _leftGyroZMinusMinBreachTime;
                gyroButton = _leftGyroZMinusButton;
                gyroComboButton = _leftGyroZMinusComboButton;
                gyroHeavyButton = _leftGyroZMinusHeavyButton;
                gyroComboEnabled = _leftGyroZMinusComboEnabled;
                gyroHeavyEnabled = _leftGyroZMinusHeavyEnabled;
                gyroSecondaryButton = _leftGyroZMinusSecondaryButton;
                gyroSecondaryButtonDelay = _leftGyroZMinusSecondaryButtonDelay;
                gyroPressType = _leftGyroZMinusPressType;
                gyroPressed = ref _leftGyroZMinusPressed;
                lastGyroTime = ref _lastLeftGyroZMinusTime;
                lastGyroMotionTime = ref _lastLeftGyroZMinusMotionTime;
                gyroComboPressed = ref _leftGyroZMinusComboPressed;
                gyroComboStartTime = ref _leftGyroZMinusComboStartTime;
                gyroOppositeThresholdBreached = ref _leftGyroZMinusOppositeThresholdBreached;
                gyroHeavyPressed = ref _leftGyroZMinusHeavyPressed;
                gyroHeavyStartTime = ref _leftGyroZMinusHeavyStartTime;
                gyroSecondPress = ref _leftGyroZMinusSecondPress;
                gyroSequentialPressState = ref _leftGyroZMinusSequentialPressState;
                lastGyroExternalCooldownTime = ref _lastLeftGyroZMinusExternalCooldownTime;
                gyroBreachStartTime = ref _leftGyroZMinusBreachStartTime;
            }
            else if (axis == Axis.X && direction == Direction.Both)
            {
                // Existing code for leftAccelX
                accelEnabled = _leftAccelXEnabled;
                accelThreshold = _leftAccelXThreshold;
                accelHeavyThreshold = _leftAccelXHeavyThreshold;
                accelCooldownDuration = _leftAccelXCooldownDuration;
                accelExternalCooldownDuration = _leftAccelXExternalCooldownDuration;
                accelPressDuration = _leftAccelXPressDuration;
                accelMinBreachTime = _leftAccelXMinBreachTime;
                accelButton = _leftAccelXButton;
                accelComboButton = _leftAccelXComboButton;
                accelHeavyButton = _leftAccelXHeavyButton;
                accelComboEnabled = _leftAccelXComboEnabled;
                accelHeavyEnabled = _leftAccelXHeavyEnabled;
                accelSecondaryButton = _leftAccelXSecondaryButton;
                accelSecondaryButtonDelay = _leftAccelXSecondaryButtonDelay;
                accelPressType = _leftAccelXPressType;
                accelPressed = ref _leftAccelXPressed;
                lastAccelTime = ref _lastLeftAccelXTime;
                lastAccelMotionTime = ref _lastLeftAccelXMotionTime;
                accelComboPressed = ref _leftAccelXComboPressed;
                accelComboStartTime = ref _leftAccelXComboStartTime;
                accelOppositeThresholdBreached = ref _leftAccelXOppositeThresholdBreached;
                accelHeavyPressed = ref _leftAccelXHeavyPressed;
                accelHeavyStartTime = ref _leftAccelXHeavyStartTime;
                accelSecondPress = ref _leftAccelXSecondPress;
                accelSequentialPressState = ref _leftAccelXSequentialPressState;
                lastAccelExternalCooldownTime = ref _lastLeftAccelXExternalCooldownTime;
                accelBreachStartTime = ref _leftAccelXBreachStartTime;
            }
        }
        else // Right Joy-Con
        {
            if (axis == Axis.All && direction == Direction.Both)
            {
                // Existing code for rightGyro and rightAccel
                gyroEnabled = _rightGyroEnabled;
                accelEnabled = _rightAccelEnabled;
                gyroThreshold = _rightGyroThreshold;
                accelThreshold = _rightAccelThreshold;
                gyroHeavyThreshold = _rightGyroHeavyThreshold;
                accelHeavyThreshold = _rightAccelHeavyThreshold;
                gyroCooldownDuration = _rightGyroCooldownDuration;
                accelCooldownDuration = _rightAccelCooldownDuration;
                gyroExternalCooldownDuration = _rightGyroExternalCooldownDuration;
                accelExternalCooldownDuration = _rightAccelExternalCooldownDuration;
                gyroPressDuration = _rightGyroPressDuration;
                accelPressDuration = _rightAccelPressDuration;
                gyroMinBreachTime = _rightGyroMinBreachTime;
                accelMinBreachTime = _rightAccelMinBreachTime;
                gyroButton = GetButtonForMotion(_rightGyroButtonP1, _rightGyroButtonP2);
                accelButton = GetButtonForMotion(_rightAccelButtonP1, _rightAccelButtonP2);
                gyroComboButton = _rightGyroComboButton;
                accelComboButton = _rightAccelComboButton;
                gyroHeavyButton = _rightGyroHeavyButton;
                accelHeavyButton = _rightAccelHeavyButton;
                gyroComboEnabled = _rightGyroComboEnabled;
                accelComboEnabled = _rightAccelComboEnabled;
                gyroHeavyEnabled = _rightGyroHeavyEnabled;
                accelHeavyEnabled = _rightAccelHeavyEnabled;
                gyroSecondaryButton = _rightGyroSecondaryButton;
                accelSecondaryButton = _rightAccelSecondaryButton;
                gyroSecondaryButtonDelay = _rightGyroSecondaryButtonDelay;
                accelSecondaryButtonDelay = _rightAccelSecondaryButtonDelay;
                gyroPressType = _rightGyroPressType;
                accelPressType = _rightAccelPressType;
                gyroPressed = ref _rightGyroPressed;
                accelPressed = ref _rightAccelPressed;
                lastGyroTime = ref _lastRightGyroTime;
                lastAccelTime = ref _lastRightAccelTime;
                lastGyroMotionTime = ref _lastRightGyroMotionTime;
                lastAccelMotionTime = ref _lastRightAccelMotionTime;
                gyroComboPressed = ref _rightGyroComboPressed;
                accelComboPressed = ref _rightAccelComboPressed;
                gyroComboStartTime = ref _rightGyroComboStartTime;
                accelComboStartTime = ref _rightAccelComboStartTime;
                gyroOppositeThresholdBreached = ref _rightGyroOppositeThresholdBreached;
                accelOppositeThresholdBreached = ref _rightAccelOppositeThresholdBreached;
                gyroHeavyPressed = ref _rightGyroHeavyPressed;
                accelHeavyPressed = ref _rightAccelHeavyPressed;
                gyroHeavyStartTime = ref _rightGyroHeavyStartTime;
                accelHeavyStartTime = ref _rightAccelHeavyStartTime;
                gyroSecondPress = ref _rightGyroSecondPress;
                accelSecondPress = ref _rightAccelSecondPress;
                gyroSequentialPressState = ref _rightGyroSequentialPressState;
                accelSequentialPressState = ref _rightAccelSequentialPressState;
                lastGyroExternalCooldownTime = ref _lastRightGyroExternalCooldownTime;
                lastAccelExternalCooldownTime = ref _lastRightAccelExternalCooldownTime;
                gyroBreachStartTime = ref _rightGyroBreachStartTime;
                accelBreachStartTime = ref _rightAccelBreachStartTime;
            }
            else if (axis == Axis.Z && direction == Direction.Both)
            {
                // Existing code for rightGyroZ
                gyroEnabled = _rightGyroZEnabled;
                gyroThreshold = _rightGyroZThreshold;
                gyroHeavyThreshold = _rightGyroZHeavyThreshold;
                gyroCooldownDuration = _rightGyroZCooldownDuration;
                gyroExternalCooldownDuration = _rightGyroZExternalCooldownDuration;
                gyroPressDuration = _rightGyroZPressDuration;
                gyroMinBreachTime = _rightGyroZMinBreachTime;
                gyroButton = _rightGyroZButton;
                gyroComboButton = _rightGyroZComboButton;
                gyroHeavyButton = _rightGyroZHeavyButton;
                gyroComboEnabled = _rightGyroZComboEnabled;
                gyroHeavyEnabled = _rightGyroZHeavyEnabled;
                gyroSecondaryButton = _rightGyroZSecondaryButton;
                gyroSecondaryButtonDelay = _rightGyroZSecondaryButtonDelay;
                gyroPressType = _rightGyroZPressType;
                gyroPressed = ref _rightGyroZPressed;
                lastGyroTime = ref _lastRightGyroZTime;
                lastGyroMotionTime = ref _lastRightGyroZMotionTime;
                gyroComboPressed = ref _rightGyroZComboPressed;
                gyroComboStartTime = ref _rightGyroZComboStartTime;
                gyroOppositeThresholdBreached = ref _rightGyroZOppositeThresholdBreached;
                gyroHeavyPressed = ref _rightGyroZHeavyPressed;
                gyroHeavyStartTime = ref _rightGyroZHeavyStartTime;
                gyroSecondPress = ref _rightGyroZSecondPress;
                gyroSequentialPressState = ref _rightGyroZSequentialPressState;
                lastGyroExternalCooldownTime = ref _lastRightGyroZExternalCooldownTime;
                gyroBreachStartTime = ref _rightGyroZBreachStartTime;
            }
            else if (axis == Axis.Z && direction == Direction.Positive)
            {
                gyroEnabled = _rightGyroZPlusEnabled;
                gyroThreshold = _rightGyroZPlusThreshold;
                gyroHeavyThreshold = _rightGyroZPlusHeavyThreshold;
                gyroCooldownDuration = _rightGyroZPlusCooldownDuration;
                gyroExternalCooldownDuration = _rightGyroZPlusExternalCooldownDuration;
                gyroPressDuration = _rightGyroZPlusPressDuration;
                gyroMinBreachTime = _rightGyroZPlusMinBreachTime;
                gyroButton = _rightGyroZPlusButton;
                gyroComboButton = _rightGyroZPlusComboButton;
                gyroHeavyButton = _rightGyroZPlusHeavyButton;
                gyroComboEnabled = _rightGyroZPlusComboEnabled;
                gyroHeavyEnabled = _rightGyroZPlusHeavyEnabled;
                gyroSecondaryButton = _rightGyroZPlusSecondaryButton;
                gyroSecondaryButtonDelay = _rightGyroZPlusSecondaryButtonDelay;
                gyroPressType = _rightGyroZPlusPressType;
                gyroPressed = ref _rightGyroZPlusPressed;
                lastGyroTime = ref _lastRightGyroZPlusTime;
                lastGyroMotionTime = ref _lastRightGyroZPlusMotionTime;
                gyroComboPressed = ref _rightGyroZPlusComboPressed;
                gyroComboStartTime = ref _rightGyroZPlusComboStartTime;
                gyroOppositeThresholdBreached = ref _rightGyroZPlusOppositeThresholdBreached;
                gyroHeavyPressed = ref _rightGyroZPlusHeavyPressed;
                gyroHeavyStartTime = ref _rightGyroZPlusHeavyStartTime;
                gyroSecondPress = ref _rightGyroZPlusSecondPress;
                gyroSequentialPressState = ref _rightGyroZPlusSequentialPressState;
                lastGyroExternalCooldownTime = ref _lastRightGyroZPlusExternalCooldownTime;
                gyroBreachStartTime = ref _rightGyroZPlusBreachStartTime;
            }
            else if (axis == Axis.Z && direction == Direction.Negative)
            {
                gyroEnabled = _rightGyroZMinusEnabled;
                gyroThreshold = _rightGyroZMinusThreshold;
                gyroHeavyThreshold = _rightGyroZMinusHeavyThreshold;
                gyroCooldownDuration = _rightGyroZMinusCooldownDuration;
                gyroExternalCooldownDuration = _rightGyroZMinusExternalCooldownDuration;
                gyroPressDuration = _rightGyroZMinusPressDuration;
                gyroMinBreachTime = _rightGyroZMinusMinBreachTime;
                gyroButton = _rightGyroZMinusButton;
                gyroComboButton = _rightGyroZMinusComboButton;
                gyroHeavyButton = _rightGyroZMinusHeavyButton;
                gyroComboEnabled = _rightGyroZMinusComboEnabled;
                gyroHeavyEnabled = _rightGyroZMinusHeavyEnabled;
                gyroSecondaryButton = _rightGyroZMinusSecondaryButton;
                gyroSecondaryButtonDelay = _rightGyroZMinusSecondaryButtonDelay;
                gyroPressType = _rightGyroZMinusPressType;
                gyroPressed = ref _rightGyroZMinusPressed;
                lastGyroTime = ref _lastRightGyroZMinusTime;
                lastGyroMotionTime = ref _lastRightGyroZMinusMotionTime;
                gyroComboPressed = ref _rightGyroZMinusComboPressed;
                gyroComboStartTime = ref _rightGyroZMinusComboStartTime;
                gyroOppositeThresholdBreached = ref _rightGyroZMinusOppositeThresholdBreached;
                gyroHeavyPressed = ref _rightGyroZMinusHeavyPressed;
                gyroHeavyStartTime = ref _rightGyroZMinusHeavyStartTime;
                gyroSecondPress = ref _rightGyroZMinusSecondPress;
                gyroSequentialPressState = ref _rightGyroZMinusSequentialPressState;
                lastGyroExternalCooldownTime = ref _lastRightGyroZMinusExternalCooldownTime;
                gyroBreachStartTime = ref _rightGyroZMinusBreachStartTime;
            }
            else if (axis == Axis.X && direction == Direction.Both)
            {
                // Existing code for rightAccelX
                accelEnabled = _rightAccelXEnabled;
                accelThreshold = _rightAccelXThreshold;
                accelHeavyThreshold = _rightAccelXHeavyThreshold;
                accelCooldownDuration = _rightAccelXCooldownDuration;
                accelExternalCooldownDuration = _rightAccelXExternalCooldownDuration;
                accelPressDuration = _rightAccelXPressDuration;
                accelMinBreachTime = _rightAccelXMinBreachTime;
                accelButton = _rightAccelXButton;
                accelComboButton = _rightAccelXComboButton;
                accelHeavyButton = _rightAccelXHeavyButton;
                accelComboEnabled = _rightAccelXComboEnabled;
                accelHeavyEnabled = _rightAccelXHeavyEnabled;
                accelSecondaryButton = _rightAccelXSecondaryButton;
                accelSecondaryButtonDelay = _rightAccelXSecondaryButtonDelay;
                accelPressType = _rightAccelXPressType;
                accelPressed = ref _rightAccelXPressed;
                lastAccelTime = ref _lastRightAccelXTime;
                lastAccelMotionTime = ref _lastRightAccelXMotionTime;
                accelComboPressed = ref _rightAccelXComboPressed;
                accelComboStartTime = ref _rightAccelXComboStartTime;
                accelOppositeThresholdBreached = ref _rightAccelXOppositeThresholdBreached;
                accelHeavyPressed = ref _rightAccelXHeavyPressed;
                accelHeavyStartTime = ref _rightAccelXHeavyStartTime;
                accelSecondPress = ref _rightAccelXSecondPress;
                accelSequentialPressState = ref _rightAccelXSequentialPressState;
                lastAccelExternalCooldownTime = ref _lastRightAccelXExternalCooldownTime;
                accelBreachStartTime = ref _rightAccelXBreachStartTime;
            }
        }

        // Return early if both gyro and accel are disabled
        if (!gyroEnabled && !accelEnabled)
        {
            return;
        }

        // Determine if thresholds are breached
        bool gyroThresholdBreached = false;
        bool accelThresholdBreached = false;
        bool gyroHeavyThresholdBreached = false;
        bool accelHeavyThresholdBreached = false;

        if (gyroEnabled)
        {
            float gyroValue = 0f;
            float gyroOppositeValue = 0f;

            if (axis == Axis.All)
            {
                gyroValue = Math.Max(Math.Max(Math.Abs(gyro.X), Math.Abs(gyro.Y)), Math.Abs(gyro.Z));
            }
            else if (axis == Axis.Z)
            {
                if (direction == Direction.Positive)
                {
                    gyroValue = gyro.Z > 0 ? gyro.Z : 0;
                }
                else if (direction == Direction.Negative)
                {
                    gyroValue = gyro.Z < 0 ? -gyro.Z : 0;
                }
                else // Direction.Both
                {
                    gyroValue = Math.Abs(gyro.Z);
                }
                gyroOppositeValue = gyro.Z;
            }

            gyroThresholdBreached = gyroValue > gyroThreshold;
            gyroHeavyThresholdBreached = gyroValue > gyroHeavyThreshold;
        }

        if (accelEnabled)
        {
            float accelValue = 0f;
            float accelOppositeValue = 0f;

            if (axis == Axis.All)
            {
                accelValue = Math.Max(Math.Max(Math.Abs(accel.X), Math.Abs(accel.Y)), Math.Abs(accel.Z));
            }
            else if (axis == Axis.X)
            {
                accelValue = Math.Abs(accel.X);
                accelOppositeValue = accel.X;
            }

            accelThresholdBreached = accelValue > accelThreshold;
            accelHeavyThresholdBreached = accelValue > accelHeavyThreshold;
        }

        // Update breach start times
        if (gyroEnabled && gyroThresholdBreached)
        {
            if (gyroBreachStartTime == 0)
            {
                gyroBreachStartTime = currentTime;
            }
        }
        else
        {
            gyroBreachStartTime = 0;
        }

        if (accelEnabled && accelThresholdBreached)
        {
            if (accelBreachStartTime == 0)
            {
                accelBreachStartTime = currentTime;
            }
        }
        else
        {
            accelBreachStartTime = 0;
        }

        // Set opposite threshold breach flags for combo feature
        if (axis == Axis.Z && gyroEnabled)
        {
            if (isLeft)
            {
                gyroOppositeThresholdBreached = false;
                if (direction == Direction.Positive)
                {
                    gyroOppositeThresholdBreached = _rightGyroZMinusBreachStartTime > 0 && (currentTime - _rightGyroZMinusBreachStartTime <= _comboWindow);
                }
                else if (direction == Direction.Negative)
                {
                    gyroOppositeThresholdBreached = _rightGyroZPlusBreachStartTime > 0 && (currentTime - _rightGyroZPlusBreachStartTime <= _comboWindow);
                }
            }
            else
            {
                gyroOppositeThresholdBreached = false;
                if (direction == Direction.Positive)
                {
                    gyroOppositeThresholdBreached = _leftGyroZMinusBreachStartTime > 0 && (currentTime - _leftGyroZMinusBreachStartTime <= _comboWindow);
                }
                else if (direction == Direction.Negative)
                {
                    gyroOppositeThresholdBreached = _leftGyroZPlusBreachStartTime > 0 && (currentTime - _leftGyroZPlusBreachStartTime <= _comboWindow);
                }
            }
        }

        // Check if minimum breach times have been met
        bool gyroDetected = gyroEnabled && gyroThresholdBreached &&
            (currentTime - gyroBreachStartTime >= gyroMinBreachTime);

        bool accelDetected = accelEnabled && accelThresholdBreached &&
            (currentTime - accelBreachStartTime >= accelMinBreachTime);

        // Check external cooldowns
        bool gyroAllowed = currentTime - lastGyroExternalCooldownTime >= gyroExternalCooldownDuration;
        bool accelAllowed = currentTime - lastAccelExternalCooldownTime >= accelExternalCooldownDuration;

        // Handle gyro motion
        if (gyroDetected && gyroAllowed)
        {
            HandleMotionForButton(isLeft, true, currentTime,
                ref gyroPressed, ref lastGyroTime, ref lastGyroMotionTime,
                gyroButton,
                gyroComboButton, ref gyroComboPressed, ref gyroComboStartTime, gyroOppositeThresholdBreached, gyroComboEnabled,
                gyroHeavyButton, gyroHeavyThreshold, ref gyroHeavyPressed, ref gyroHeavyStartTime, gyroHeavyThresholdBreached, gyroHeavyEnabled,
                gyroSecondaryButton, gyroSecondaryButtonDelay,
                gyroPressDuration, gyroCooldownDuration, gyroPressType, ref gyroSecondPress, ref gyroSequentialPressState);

            // Trigger external cooldown
            lastGyroExternalCooldownTime = currentTime;
        }

        // Handle accel motion
        if (accelDetected && accelAllowed)
        {
            HandleMotionForButton(isLeft, true, currentTime,
                ref accelPressed, ref lastAccelTime, ref lastAccelMotionTime,
                accelButton,
                accelComboButton, ref accelComboPressed, ref accelComboStartTime, accelOppositeThresholdBreached, accelComboEnabled,
                accelHeavyButton, accelHeavyThreshold, ref accelHeavyPressed, ref accelHeavyStartTime, accelHeavyThresholdBreached, accelHeavyEnabled,
                accelSecondaryButton, accelSecondaryButtonDelay,
                accelPressDuration, accelCooldownDuration, accelPressType, ref accelSecondPress, ref accelSequentialPressState);

            // Trigger external cooldown
            lastAccelExternalCooldownTime = currentTime;
        }

        // Handle button releases
        if (!gyroDetected || !gyroAllowed)
        {
            HandleMotionForButton(isLeft, false, currentTime,
                ref gyroPressed, ref lastGyroTime, ref lastGyroMotionTime,
                gyroButton,
                gyroComboButton, ref gyroComboPressed, ref gyroComboStartTime, gyroOppositeThresholdBreached, gyroComboEnabled,
                gyroHeavyButton, gyroHeavyThreshold, ref gyroHeavyPressed, ref gyroHeavyStartTime, gyroHeavyThresholdBreached, gyroHeavyEnabled,
                gyroSecondaryButton, gyroSecondaryButtonDelay,
                gyroPressDuration, gyroCooldownDuration, gyroPressType, ref gyroSecondPress, ref gyroSequentialPressState);
        }

        if (!accelDetected || !accelAllowed)
        {
            HandleMotionForButton(isLeft, false, currentTime,
                ref accelPressed, ref lastAccelTime, ref lastAccelMotionTime,
                accelButton,
                accelComboButton, ref accelComboPressed, ref accelComboStartTime, accelOppositeThresholdBreached, accelComboEnabled,
                accelHeavyButton, accelHeavyThreshold, ref accelHeavyPressed, ref accelHeavyStartTime, accelHeavyThresholdBreached, accelHeavyEnabled,
                accelSecondaryButton, accelSecondaryButtonDelay,
                accelPressDuration, accelCooldownDuration, accelPressType, ref accelSecondPress, ref accelSequentialPressState);
        }
    }

    private void HandleMotionForButton(bool isLeft, bool motionDetected, long currentTime,
        ref bool buttonPressed, ref long lastPressTime, ref long lastMotionTime,
        Button primaryButton,
        Button comboButton, ref bool comboPressed, ref long comboStartTime, bool oppositeThresholdBreached, bool comboEnabled,
        Button heavyButton, float heavyThreshold, ref bool heavyPressed, ref long heavyStartTime, bool heavyThresholdBreached, bool heavyEnabled,
        Button? secondaryButton, long secondaryButtonDelay, long pressDuration, long cooldownDuration,
        PressType pressType, ref bool secondPress, ref SequentialPressState sequentialPressState)
    {
        switch (pressType)
        {
            case PressType.Single:
                HandleSinglePress(motionDetected, ref buttonPressed, ref lastPressTime,
                    primaryButton,
                    comboButton, ref comboPressed, ref comboStartTime, oppositeThresholdBreached, comboEnabled,
                    heavyButton, heavyThreshold, ref heavyPressed, ref heavyStartTime, heavyThresholdBreached, heavyEnabled,
                    secondaryButton, secondaryButtonDelay,
                    pressDuration, cooldownDuration, currentTime);
                break;
            case PressType.Continuous:
                HandleContinuousPress(motionDetected, ref buttonPressed, ref lastPressTime, ref lastMotionTime,
                    primaryButton,
                    comboButton, ref comboPressed, ref comboStartTime, oppositeThresholdBreached, comboEnabled,
                    heavyButton, heavyThreshold, ref heavyPressed, ref heavyStartTime, heavyThresholdBreached, heavyEnabled,
                    secondaryButton, secondaryButtonDelay,
                    pressDuration, cooldownDuration, currentTime);
                break;
            case PressType.Double:
                HandleDoublePress(motionDetected, ref buttonPressed, ref lastPressTime,
                    primaryButton,
                    comboButton, ref comboPressed, ref comboStartTime, oppositeThresholdBreached, comboEnabled,
                    heavyButton, heavyThreshold, ref heavyPressed, ref heavyStartTime, heavyThresholdBreached, heavyEnabled,
                    secondaryButton, secondaryButtonDelay,
                    pressDuration, cooldownDuration, currentTime, ref sequentialPressState);
                break;
        }
    }

    private void HandleSinglePress(bool motionDetected, ref bool buttonPressed, ref long lastPressTime,
        Button primaryButton,
        Button comboButton, ref bool comboPressed, ref long comboStartTime, bool oppositeThresholdBreached, bool comboEnabled,
        Button heavyButton, float heavyThreshold, ref bool heavyPressed, ref long heavyStartTime, bool heavyThresholdBreached, bool heavyEnabled,
        Button? secondaryButton, long secondaryButtonDelay, long pressDuration, long cooldownDuration, long currentTime)
    {
        // Removed the local declaration of heavyEnabled
        if (!buttonPressed && !comboPressed && !heavyPressed)
        {
            bool cooldownComplete = currentTime - lastPressTime >= (pressDuration + cooldownDuration);

            if (motionDetected && cooldownComplete)
            {
                if (comboEnabled && comboStartTime == 0)
                {
                    // Start the combo window
                    comboStartTime = currentTime;
                }
                else if (heavyEnabled && heavyStartTime == 0)
                {
                    // Start the heavy press window
                    heavyStartTime = currentTime;
                }
                else if (!comboEnabled && !heavyEnabled)
                {
                    // Regular press when neither combo nor heavy is enabled
                    PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                    buttonPressed = true;
                    lastPressTime = currentTime;
                }
            }

            // Handle combo press detection
            if (comboEnabled)
            {
                if (oppositeThresholdBreached && comboStartTime != 0 && (currentTime - comboStartTime <= _comboWindow))
                {
                    // Opposite threshold breached within the window
                    PressButtons(comboButton, secondaryButton, secondaryButtonDelay);
                    comboPressed = true;
                    lastPressTime = currentTime;
                    comboStartTime = 0;
                }
                else if (comboStartTime != 0 && (currentTime - comboStartTime > _comboWindow))
                {
                    // Combo window expired without opposite threshold breach
                    if (heavyEnabled && heavyStartTime == 0)
                    {
                        // Start heavy press window
                        heavyStartTime = currentTime;
                    }
                    else if (!heavyEnabled)
                    {
                        // Trigger regular press
                        PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                        buttonPressed = true;
                        lastPressTime = currentTime;
                        comboStartTime = 0;
                    }
                }
            }

            // Handle heavy press detection
            if (heavyEnabled)
            {
                if (heavyThresholdBreached && heavyStartTime != 0 && (currentTime - heavyStartTime <= _heavyPressWindow))
                {
                    // Heavy press detected within the window
                    PressButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                    heavyPressed = true;
                    lastPressTime = currentTime;
                    heavyStartTime = 0;
                }
                else if (heavyStartTime != 0 && (currentTime - heavyStartTime > _heavyPressWindow))
                {
                    // Heavy press window expired without heavy press
                    PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                    buttonPressed = true;
                    lastPressTime = currentTime;
                    heavyStartTime = 0;
                }
            }
        }
        else if (buttonPressed || comboPressed || heavyPressed)
        {
            // Release the button after pressDuration
            if (currentTime - lastPressTime >= pressDuration)
            {
                if (comboPressed)
                {
                    ReleaseButtons(comboButton, secondaryButton, secondaryButtonDelay);
                    comboPressed = false;
                }
                else if (heavyPressed)
                {
                    ReleaseButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                    heavyPressed = false;
                }
                else
                {
                    ReleaseButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                    buttonPressed = false;
                }
            }
        }

        // Reset windows if motion stops and we're outside the respective windows without any press
        if (!motionDetected)
        {
            if (comboStartTime != 0 && (currentTime - comboStartTime > _comboWindow))
            {
                comboStartTime = 0;
            }
            if (heavyStartTime != 0 && (currentTime - heavyStartTime > _heavyPressWindow))
            {
                heavyStartTime = 0;
            }
        }
    }

    private void HandleContinuousPress(bool motionDetected, ref bool buttonPressed, ref long lastPressTime, ref long lastMotionTime,
        Button primaryButton,
        Button comboButton, ref bool comboPressed, ref long comboStartTime, bool oppositeThresholdBreached, bool comboEnabled,
        Button heavyButton, float heavyThreshold, ref bool heavyPressed, ref long heavyStartTime, bool heavyThresholdBreached, bool heavyEnabled,
        Button? secondaryButton, long secondaryButtonDelay, long pressDuration, long cooldownDuration, long currentTime)
    {
        // Removed the local declaration of heavyEnabled

        if (motionDetected)
        {
            lastMotionTime = currentTime;
            bool cooldownComplete = currentTime - lastPressTime >= (pressDuration + cooldownDuration);

            if (!buttonPressed && !comboPressed && !heavyPressed && cooldownComplete)
            {
                if (comboEnabled)
                {
                    if (comboStartTime == 0)
                    {
                        comboStartTime = currentTime;
                    }

                    if (oppositeThresholdBreached && (currentTime - comboStartTime) <= _comboWindow)
                    {
                        // Opposite threshold breached within the window
                        PressButtons(comboButton, secondaryButton, secondaryButtonDelay);
                        comboPressed = true;
                        lastPressTime = currentTime;
                    }
                    else if ((currentTime - comboStartTime) > _comboWindow)
                    {
                        if (heavyEnabled && heavyStartTime == 0)
                        {
                            heavyStartTime = currentTime;
                        }
                        else if (!heavyEnabled)
                        {
                            // Regular press
                            PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                            buttonPressed = true;
                            lastPressTime = currentTime;
                        }
                    }
                }
                else if (heavyEnabled)
                {
                    if (heavyStartTime == 0)
                    {
                        heavyStartTime = currentTime;
                    }

                    if (heavyThresholdBreached && (currentTime - heavyStartTime) <= _heavyPressWindow)
                    {
                        // Heavy press detected within the window
                        PressButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                        heavyPressed = true;
                        lastPressTime = currentTime;
                    }
                    else if ((currentTime - heavyStartTime) > _heavyPressWindow)
                    {
                        // Regular press
                        PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                        buttonPressed = true;
                        lastPressTime = currentTime;
                    }
                }
                else
                {
                    // Regular press when neither combo nor heavy is enabled
                    PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                    buttonPressed = true;
                    lastPressTime = currentTime;
                }
            }
        }
        else if ((buttonPressed || comboPressed || heavyPressed) && (currentTime - lastMotionTime) >= pressDuration)
        {
            if (comboPressed)
            {
                ReleaseButtons(comboButton, secondaryButton, secondaryButtonDelay);
                comboPressed = false;
            }
            else if (heavyPressed)
            {
                ReleaseButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                heavyPressed = false;
            }
            else
            {
                ReleaseButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                buttonPressed = false;
            }
            comboStartTime = 0;
            heavyStartTime = 0;
        }
    }

    private void HandleDoublePress(bool motionDetected, ref bool buttonPressed, ref long lastPressTime,
        Button primaryButton,
        Button comboButton, ref bool comboPressed, ref long comboStartTime, bool oppositeThresholdBreached, bool comboEnabled,
        Button heavyButton, float heavyThreshold, ref bool heavyPressed, ref long heavyStartTime, bool heavyThresholdBreached, bool heavyEnabled,
        Button? secondaryButton, long secondaryButtonDelay, long pressDuration, long cooldownDuration,
        long currentTime, ref SequentialPressState state)
    {
        // Removed the local declaration of heavyEnabled
        const long gapBetweenPresses = 75; // ms

        switch (state)
        {
            case SequentialPressState.Idle:
                if (motionDetected && (currentTime - lastPressTime >= (pressDuration + cooldownDuration)))
                {
                    if (comboEnabled)
                    {
                        comboStartTime = currentTime;
                    }
                    else if (heavyEnabled)
                    {
                        heavyStartTime = currentTime;
                    }
                    state = SequentialPressState.FirstPress;
                }
                break;

            case SequentialPressState.FirstPress:
                if (comboEnabled)
                {
                    if (currentTime - comboStartTime > _comboWindow)
                    {
                        bool isComboPress = oppositeThresholdBreached;
                        if (isComboPress)
                        {
                            PressButtons(comboButton, secondaryButton, secondaryButtonDelay);
                            comboPressed = true;
                        }
                        else if (heavyEnabled)
                        {
                            if (currentTime - heavyStartTime > _heavyPressWindow)
                            {
                                bool isHeavyPress = heavyThresholdBreached;
                                if (isHeavyPress)
                                {
                                    PressButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                                    heavyPressed = true;
                                }
                                else
                                {
                                    PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                                    buttonPressed = true;
                                }
                            }
                        }
                        else
                        {
                            PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                            buttonPressed = true;
                        }
                        lastPressTime = currentTime;
                        state = SequentialPressState.BetweenFirstAndSecond;
                    }
                }
                else if (heavyEnabled)
                {
                    if (currentTime - heavyStartTime > _heavyPressWindow)
                    {
                        bool isHeavyPress = heavyThresholdBreached;
                        if (isHeavyPress)
                        {
                            PressButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                            heavyPressed = true;
                        }
                        else
                        {
                            PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                            buttonPressed = true;
                        }
                        lastPressTime = currentTime;
                        state = SequentialPressState.BetweenFirstAndSecond;
                    }
                }
                else
                {
                    PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                    buttonPressed = true;
                    lastPressTime = currentTime;
                    state = SequentialPressState.BetweenFirstAndSecond;
                }
                break;

            case SequentialPressState.BetweenFirstAndSecond:
                if (currentTime - lastPressTime >= pressDuration)
                {
                    if (comboPressed)
                    {
                        ReleaseButtons(comboButton, secondaryButton, secondaryButtonDelay);
                        comboPressed = false;
                    }
                    else if (heavyPressed)
                    {
                        ReleaseButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                        heavyPressed = false;
                    }
                    else
                    {
                        ReleaseButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                        buttonPressed = false;
                    }

                    if (motionDetected && (currentTime - lastPressTime >= (pressDuration + gapBetweenPresses)))
                    {
                        if (comboEnabled)
                        {
                            comboStartTime = currentTime;
                        }
                        else if (heavyEnabled)
                        {
                            heavyStartTime = currentTime;
                        }
                        state = SequentialPressState.SecondPress;
                    }
                    else if (currentTime - lastPressTime >= (pressDuration + cooldownDuration))
                    {
                        state = SequentialPressState.Idle;
                    }
                }
                break;

            case SequentialPressState.SecondPress:
                if (comboEnabled)
                {
                    if (currentTime - comboStartTime > _comboWindow)
                    {
                        bool isComboPress = oppositeThresholdBreached;
                        if (isComboPress)
                        {
                            PressButtons(comboButton, secondaryButton, secondaryButtonDelay);
                            comboPressed = true;
                        }
                        else if (heavyEnabled)
                        {
                            if (currentTime - heavyStartTime > _heavyPressWindow)
                            {
                                bool isHeavyPress = heavyThresholdBreached;
                                if (isHeavyPress)
                                {
                                    PressButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                                    heavyPressed = true;
                                }
                                else
                                {
                                    PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                                    buttonPressed = true;
                                }
                            }
                        }
                        else
                        {
                            PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                            buttonPressed = true;
                        }
                        lastPressTime = currentTime;
                        state = SequentialPressState.Cooldown;
                    }
                }
                else if (heavyEnabled)
                {
                    if (currentTime - heavyStartTime > _heavyPressWindow)
                    {
                        bool isHeavyPress = heavyThresholdBreached;
                        if (isHeavyPress)
                        {
                            PressButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                            heavyPressed = true;
                        }
                        else
                        {
                            PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                            buttonPressed = true;
                        }
                        lastPressTime = currentTime;
                        state = SequentialPressState.Cooldown;
                    }
                }
                else
                {
                    PressButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                    buttonPressed = true;
                    lastPressTime = currentTime;
                    state = SequentialPressState.Cooldown;
                }
                break;

            case SequentialPressState.Cooldown:
                if (currentTime - lastPressTime >= pressDuration)
                {
                    if (comboPressed)
                    {
                        ReleaseButtons(comboButton, secondaryButton, secondaryButtonDelay);
                        comboPressed = false;
                    }
                    else if (heavyPressed)
                    {
                        ReleaseButtons(heavyButton, secondaryButton, secondaryButtonDelay);
                        heavyPressed = false;
                    }
                    else
                    {
                        ReleaseButtons(primaryButton, secondaryButton, secondaryButtonDelay);
                        buttonPressed = false;
                    }

                    if (currentTime - lastPressTime >= (pressDuration + cooldownDuration))
                    {
                        state = SequentialPressState.Idle;
                    }
                }
                break;
        }
    }

    private async void PressButtons(Button primaryButton, Button? secondaryButton, long secondaryButtonDelay)
    {
        _buttonsMotion[(int)primaryButton] = true;
        UpdateInput();

        if (secondaryButton.HasValue)
        {
            if (secondaryButtonDelay > 0)
            {
                await Task.Delay((int)secondaryButtonDelay);
            }
            _buttonsMotion[(int)secondaryButton.Value] = true;
            UpdateInput();
        }
    }

    private async void ReleaseButtons(Button primaryButton, Button? secondaryButton, long secondaryButtonDelay)
    {
        _buttonsMotion[(int)primaryButton] = false;
        UpdateInput();

        if (secondaryButton.HasValue)
        {
            if (secondaryButtonDelay > 0)
            {
                await Task.Delay((int)secondaryButtonDelay);
            }
            _buttonsMotion[(int)secondaryButton.Value] = false;
            UpdateInput();
        }
    }

    private void Simulate(string s, bool click = true, bool up = false)
    {
        if (s.StartsWith("key_"))
        {
            var key = (KeyCode)int.Parse(s.AsSpan(4));
            if (click)
            {
                WindowsInput.Simulate.Events().Click(key).Invoke();
            }
            else
            {
                if (up)
                {
                    WindowsInput.Simulate.Events().Release(key).Invoke();
                }
                else
                {
                    WindowsInput.Simulate.Events().Hold(key).Invoke();
                }
            }
        }
        else if (s.StartsWith("mse_"))
        {
            var button = (ButtonCode)int.Parse(s.AsSpan(4));
            if (click)
            {
                WindowsInput.Simulate.Events().Click(button).Invoke();
            }
            else
            {
                if (Config.DragToggle)
                {
                    if (!up)
                    {
                        bool release;
                        _mouseToggleBtn.TryGetValue((int)button, out release);
                        if (release)
                        {
                            WindowsInput.Simulate.Events().Release(button).Invoke();
                        }
                        else
                        {
                            WindowsInput.Simulate.Events().Hold(button).Invoke();
                        }

                        _mouseToggleBtn[(int)button] = !release;
                    }
                }
                else
                {
                    if (up)
                    {
                        WindowsInput.Simulate.Events().Release(button).Invoke();
                    }
                    else
                    {
                        WindowsInput.Simulate.Events().Hold(button).Invoke();
                    }
                }
            }
        }
    }

    // For Joystick->Joystick inputs
    private void SimulateContinous(int origin, string s)
    {
        SimulateContinous(_buttons[origin], s);
    }

    private void SimulateContinous(bool pressed, string s)
    {
        if (s.StartsWith("joy_"))
        {
            var button = int.Parse(s.AsSpan(4));

            if (IsJoined && !IsLeft)
            {
                button = FlipButton(button);
            }

            _buttonsRemapped[button] |= pressed;
        }
    }

    private int FlipButton(int button)
    {
        return button switch
        {
            (int)Button.DpadDown => (int)Button.B,
            (int)Button.DpadRight => (int)Button.A,
            (int)Button.DpadUp => (int)Button.X,
            (int)Button.DpadLeft => (int)Button.Y,
            (int)Button.B => (int)Button.DpadDown,
            (int)Button.A => (int)Button.DpadRight,
            (int)Button.X => (int)Button.DpadUp,
            (int)Button.Y => (int)Button.DpadLeft,
            _ => button
        };
    }

    private void ReleaseRemappedButtons()
    {
        // overwrite custom-mapped buttons
        if (Settings.Value("capture") != "0")
        {
            _buttonsRemapped[(int)Button.Capture] = false;
        }

        if (Settings.Value("home") != "0")
        {
            _buttonsRemapped[(int)Button.Home] = false;
        }

        // single joycon mode
        if (IsLeft)
        {
            if (Settings.Value("sl_l") != "0")
            {
                _buttonsRemapped[(int)Button.SL] = false;
            }

            if (Settings.Value("sr_l") != "0")
            {
                _buttonsRemapped[(int)Button.SR] = false;
            }
        }
        else
        {
            if (Settings.Value("sl_r") != "0")
            {
                _buttonsRemapped[(int)Button.SL] = false;
            }

            if (Settings.Value("sr_r") != "0")
            {
                _buttonsRemapped[(int)Button.SR] = false;
            }
        }
    }

    private void SimulateRemappedButtons()
    {
        // Handle only physical button presses
        if (_buttonsDown[(int)Button.Capture])
        {
            Simulate(Settings.Value("capture"), false);
        }

        if (_buttonsUp[(int)Button.Capture])
        {
            Simulate(Settings.Value("capture"), false, true);
        }

        if (_buttonsDown[(int)Button.Home])
        {
            Simulate(Settings.Value("home"), false);
        }

        if (_buttonsUp[(int)Button.Home])
        {
            Simulate(Settings.Value("home"), false, true);
        }

        SimulateContinous((int)Button.Capture, Settings.Value("capture"));
        SimulateContinous((int)Button.Home, Settings.Value("home"));

        if (IsLeft)
        {
            if (_buttonsDown[(int)Button.SL])
            {
                Simulate(Settings.Value("sl_l"), false);
            }

            if (_buttonsUp[(int)Button.SL])
            {
                Simulate(Settings.Value("sl_l"), false, true);
            }

            if (_buttonsDown[(int)Button.SR])
            {
                Simulate(Settings.Value("sr_l"), false);
            }

            if (_buttonsUp[(int)Button.SR])
            {
                Simulate(Settings.Value("sr_l"), false, true);
            }
        }
        else
        {
            if (_buttonsDown[(int)Button.SL])
            {
                Simulate(Settings.Value("sl_r"), false);
            }

            if (_buttonsUp[(int)Button.SL])
            {
                Simulate(Settings.Value("sl_r"), false, true);
            }

            if (_buttonsDown[(int)Button.SR])
            {
                Simulate(Settings.Value("sr_r"), false);
            }

            if (_buttonsUp[(int)Button.SR])
            {
                Simulate(Settings.Value("sr_r"), false, true);
            }
        }

        if (IsLeft || IsJoined)
        {
            var controller = IsLeft ? this : Other;
            SimulateContinous(controller._buttons[(int)Button.SL], Settings.Value("sl_l"));
            SimulateContinous(controller._buttons[(int)Button.SR], Settings.Value("sr_l"));
        }

        if (!IsLeft || IsJoined)
        {
            var controller = !IsLeft ? this : Other;
            SimulateContinous(controller._buttons[(int)Button.SL], Settings.Value("sl_r"));
            SimulateContinous(controller._buttons[(int)Button.SR], Settings.Value("sr_r"));
        }

        bool hasShaked = IsPrimaryGyro ? _hasShaked : Other._hasShaked;
        SimulateContinous(hasShaked, Settings.Value("shake"));
    }

    private void RemapButtons()
    {
        lock (_buttonsRemapped)
        {
            lock (_buttons)
            {
                // Copy physical button states
                Array.Copy(_buttons, _buttonsRemapped, _buttons.Length);

                // Overlay motion-induced button presses
                for (int i = 0; i < _buttons.Length; i++)
                {
                    if (_buttonsMotion[i])
                    {
                        _buttonsRemapped[i] = true;
                    }
                }

                ReleaseRemappedButtons();
                SimulateRemappedButtons();
            }
        }
    }

    // 4. Optional: Method to reset motion buttons
    public void ResetMotionButtons()
    {
        lock (_buttonsMotion)
        {
            Array.Clear(_buttonsMotion, 0, _buttonsMotion.Length);
        }
        UpdateInput();
    }

    private static bool HandleJoyAction(string settingKey, out int button)
    {
        var resVal = Settings.Value(settingKey);
        if (resVal.StartsWith("joy_") && int.TryParse(resVal.AsSpan(4), out button))
        {
            return true;
        }

        button = 0;
        return false;
    }

    private bool IsButtonDown(int button)
    {
        return _buttonsDown[button] || (Other != null && Other._buttonsDown[button]);
    }

    private bool IsButtonUp(int button)
    {
        return _buttonsUp[button] || (Other != null && Other._buttonsUp[button]);
    }

    private void DoThingsWithButtons()
    {
        var powerOffButton = (int)(IsPro || !IsLeft || IsJoined ? Button.Home : Button.Capture);
        var timestampNow = Stopwatch.GetTimestamp();

        if (!IsUSB)
        {
            bool powerOff = false;

            if (Config.HomeLongPowerOff && _buttons[powerOffButton])
            {
                var powerOffPressedDurationMs = (timestampNow - _buttonsDownTimestamp[powerOffButton]) / 10000;
                if (powerOffPressedDurationMs > 2000)
                {
                    powerOff = true;
                }
            }

            if (Config.PowerOffInactivityMins > 0)
            {
                var timeSinceActivityMs = (timestampNow - _timestampActivity) / 10000;
                if (timeSinceActivityMs > Config.PowerOffInactivityMins * 60 * 1000)
                {
                    powerOff = true;
                }
            }

            if (powerOff)
            {
                if (IsJoined)
                {
                    Program.Mgr.PowerOff(Other);
                }
                PowerOff();
                return;
            }
        }

        if (IsJoycon && !_calibrateSticks && !_calibrateIMU)
        {
            if (Config.ChangeOrientationDoubleClick && _buttonsDown[(int)Button.LS] && _lastDoubleClick != -1)
            {
                if (_buttonsDownTimestamp[(int)Button.LS] - _lastDoubleClick < 3000000)
                {
                    Program.Mgr.JoinOrSplitJoycon(this);

                    _lastDoubleClick = _buttonsDownTimestamp[(int)Button.LS];
                    return;
                }

                _lastDoubleClick = _buttonsDownTimestamp[(int)Button.LS];
            }
            else if (Config.ChangeOrientationDoubleClick && _buttonsDown[(int)Button.LS])
            {
                _lastDoubleClick = _buttonsDownTimestamp[(int)Button.LS];
            }
        }

        RemapButtons();

        if (HandleJoyAction("swap_ab", out int button) && IsButtonDown(button))
        {
            Config.SwapAB = !Config.SwapAB;
        }

        if (HandleJoyAction("swap_xy", out button) && IsButtonDown(button))
        {
            Config.SwapXY = !Config.SwapXY;
        }

        if (HandleJoyAction("active_gyro", out button))
        {
            if (Config.GyroHoldToggle)
            {
                if (IsButtonDown(button))
                {
                    ActiveGyro = true;
                }
                else if (IsButtonUp(button))
                {
                    ActiveGyro = false;
                }
            }
            else
            {
                if (IsButtonDown(button))
                {
                    ActiveGyro = !ActiveGyro;
                }
            }
        }

        // Filtered IMU data
        _AHRS.GetEulerAngles(_curRotation);
        float dt = _avgReceiveDeltaMs.GetAverage() / 1000;

        if (Config.GyroAnalogSliders && (Other != null || IsPro))
        {
            var leftT = IsLeft ? Button.LT : Button.RT;
            var rightT = IsLeft ? Button.RT : Button.LT;
            var left = IsLeft || IsPro ? this : Other;
            var right = !IsLeft || IsPro ? this : Other;

            int ldy, rdy;
            if (Config.UseFilteredIMU)
            {
                ldy = (int)(Config.GyroAnalogSensitivity * (left._curRotation[0] - left._curRotation[3]));
                rdy = (int)(Config.GyroAnalogSensitivity * (right._curRotation[0] - right._curRotation[3]));
            }
            else
            {
                ldy = (int)(Config.GyroAnalogSensitivity * (left._gyrG.Y * dt));
                rdy = (int)(Config.GyroAnalogSensitivity * (right._gyrG.Y * dt));
            }

            if (_buttons[(int)leftT])
            {
                _sliderVal[0] = (byte)Math.Clamp(_sliderVal[0] + ldy, 0, byte.MaxValue);
            }
            else
            {
                _sliderVal[0] = 0;
            }

            if (_buttons[(int)rightT])
            {
                _sliderVal[1] = (byte)Math.Clamp(_sliderVal[1] + rdy, 0, byte.MaxValue);
            }
            else
            {
                _sliderVal[1] = 0;
            }
        }

        if (IsPrimaryGyro)
        {
            if (Config.ExtraGyroFeature.StartsWith("joy"))
            {
                if (Settings.Value("active_gyro") == "0" || ActiveGyro)
                {
                    var controlStick = Config.ExtraGyroFeature == "joy_left" ? _stick : _stick2;

                    float dx, dy;
                    if (Config.UseFilteredIMU)
                    {
                        dx = Config.GyroStickSensitivityX * (_curRotation[1] - _curRotation[4]); // yaw
                        dy = -(Config.GyroStickSensitivityY * (_curRotation[0] - _curRotation[3])); // pitch
                    }
                    else
                    {
                        dx = Config.GyroStickSensitivityX * (_gyrG.Z * dt); // yaw
                        dy = -(Config.GyroStickSensitivityY * (_gyrG.Y * dt)); // pitch
                    }

                    controlStick[0] = Math.Clamp(controlStick[0] / Config.GyroStickReduction + dx, -1.0f, 1.0f);
                    controlStick[1] = Math.Clamp(controlStick[1] / Config.GyroStickReduction + dy, -1.0f, 1.0f);
                }
            }
            else if (Config.ExtraGyroFeature == "mouse")
            {
                // gyro data is in degrees/s
                if (Settings.Value("active_gyro") == "0" || ActiveGyro)
                {
                    int dx, dy;

                    if (Config.UseFilteredIMU)
                    {
                        dx = (int)(Config.GyroMouseSensitivityX * (_curRotation[1] - _curRotation[4])); // yaw
                        dy = (int)-(Config.GyroMouseSensitivityY * (_curRotation[0] - _curRotation[3])); // pitch
                    }
                    else
                    {
                        dx = (int)(Config.GyroMouseSensitivityX * (_gyrG.Z * dt));
                        dy = (int)-(Config.GyroMouseSensitivityY * (_gyrG.Y * dt));
                    }

                    WindowsInput.Simulate.Events().MoveBy(dx, dy).Invoke();
                }

                // reset mouse position to centre of primary monitor
                if (HandleJoyAction("reset_mouse", out button) && IsButtonDown(button))
                {
                    WindowsInput.Simulate.Events()
                                .MoveTo(
                                    Screen.PrimaryScreen.Bounds.Width / 2,
                                    Screen.PrimaryScreen.Bounds.Height / 2
                                )
                                .Invoke();
                }
            }
        }
    }

    private void GetBatteryInfos(ReadOnlySpan<byte> reportBuf)
    {
        byte packetType = reportBuf[0];
        if (packetType != (byte)ReportMode.StandardFull)
        {
            return;
        }

        var prevBattery = Battery;
        var prevCharging = Charging;

        byte highNibble = (byte)(reportBuf[2] >> 4);
        Battery = (BatteryLevel)(Math.Clamp(highNibble >> 1, (byte)BatteryLevel.Empty, (byte)BatteryLevel.Full));
        Charging = (highNibble & 0x1) == 1;

        if (prevBattery != Battery)
        {
            BatteryChanged();
        }

        if (prevCharging != Charging)
        {
            ChargingChanged();
        }
    }

    private void SendCommands(CancellationToken token)
    {
        Span<byte> buf = stackalloc byte[_CommandLength];
        buf.Clear();

        // the home light stays on for 2625ms, set to less than half in case of packet drop
        const int sendHomeLightIntervalMs = 1250;
        Stopwatch timeSinceHomeLight = new();

        while (IsDeviceReady)
        {
            token.ThrowIfCancellationRequested();

            if (Program.IsSuspended)
            {
                Thread.Sleep(10);
                continue;
            }

            _sendCommandsPaused = _pauseSendCommands;
            if (_sendCommandsPaused)
            {
                Thread.Sleep(10);
                continue;
            }

            if (Config.HomeLEDOn && (timeSinceHomeLight.ElapsedMilliseconds > sendHomeLightIntervalMs || !timeSinceHomeLight.IsRunning))
            {
                SetHomeLight(Config.HomeLEDOn);
                timeSinceHomeLight.Restart();
            }

            while (_rumbles.TryDequeue(out var rumbleData))
            {
                SendRumble(buf, rumbleData);
            }

            Thread.Sleep(5);
        }
    }

    private void ReceiveReports(CancellationToken token)
    {
        Span<byte> buf = stackalloc byte[ReportLength];
        buf.Clear();

        int dropAfterMs = IsUSB ? 1500 : 3000;
        Stopwatch timeSinceError = new();
        int reconnectAttempts = 0;

        // For IMU timestamp calculation
        _avgReceiveDeltaMs.Clear();
        _avgReceiveDeltaMs.AddValue(15); // default value of 15ms between packets
        _timeSinceReceive.Reset();
        Timestamp = 0;

        while (IsDeviceReady)
        {
            token.ThrowIfCancellationRequested();

            if (Program.IsSuspended)
            {
                Thread.Sleep(10);
                continue;
            }

            // Attempt reconnection, we interrupt the thread send commands to improve the reliability
            // and to avoid thread safety issues with hidapi as we're doing both read/write
            if (timeSinceError.ElapsedMilliseconds > dropAfterMs)
            {
                if (IsUSB && reconnectAttempts >= 3)
                {
                    Log("Dropped.", Logger.LogLevel.Warning);
                    State = Status.Errored;
                    continue;
                }

                _pauseSendCommands = true;
                if (!_sendCommandsPaused)
                {
                    Thread.Sleep(10);
                    continue;
                }

                if (IsUSB)
                {
                    Log("Attempt soft reconnect...");
                    try
                    {
                        USBPairing();
                        SetReportMode(ReportMode.StandardFull);
                        SetLEDByPadID();
                    }
                    // ignore and retry
                    catch (Exception e)
                    {
                        Log("Soft reconnect failed.", e, Logger.LogLevel.Debug);
                    }
                }
                else
                {
                    //Log("Attempt soft reconnect...");
                    SetReportMode(ReportMode.StandardFull, false);
                }

                ++reconnectAttempts;
                timeSinceError.Restart();
            }

            // Receive controller data
            var error = ReceiveRaw(buf);

            if (error == ReceiveError.None && IsDeviceReady)
            {
                State = Status.IMUDataOk;
                timeSinceError.Reset();
                reconnectAttempts = 0;
                _pauseSendCommands = false;
            }
            else if (error == ReceiveError.InvalidHandle)
            {
                // should not happen
                Log("Dropped (invalid handle).", Logger.LogLevel.Error);
                State = Status.Errored;
            }
            else
            {
                timeSinceError.Start();

                // No data read, read error or invalid packet
                if (error == ReceiveError.ReadError)
                {
                    Thread.Sleep(5); // to avoid spin
                }
            }
        }
    }

    private static ushort Scale16bitsTo12bits(int value)
    {
        const float scale16bitsTo12bits = 4095f / 65535f;

        return (ushort)MathF.Round(value * scale16bitsTo12bits);
    }

    private void ExtractSticksValues(ReadOnlySpan<byte> reportBuf)
    {
        byte reportType = reportBuf[0];

        if (reportType == (byte)ReportMode.StandardFull)
        {
            var offset = IsLeft ? 0 : 3;

            _stickPrecal[0] = (ushort)(reportBuf[6 + offset] | ((reportBuf[7 + offset] & 0xF) << 8));
            _stickPrecal[1] = (ushort)((reportBuf[7 + offset] >> 4) | (reportBuf[8 + offset] << 4));

            if (IsPro)
            {
                _stick2Precal[0] = (ushort)(reportBuf[9] | ((reportBuf[10] & 0xF) << 8));
                _stick2Precal[1] = (ushort)((reportBuf[10] >> 4) | (reportBuf[11] << 4));
            }
        }
        else if (reportType == (byte)ReportMode.SimpleHID)
        {
            if (IsPro)
            {
                // Scale down to 12 bits to match the calibrations datas precision
                // Invert y axis by substracting from 0xFFFF to match 0x30 reports 
                _stickPrecal[0] = Scale16bitsTo12bits(reportBuf[4] | (reportBuf[5] << 8));
                _stickPrecal[1] = Scale16bitsTo12bits(0XFFFF - (reportBuf[6] | (reportBuf[7] << 8)));

                _stick2Precal[0] = Scale16bitsTo12bits(reportBuf[8] | (reportBuf[9] << 8));
                _stick2Precal[1] = Scale16bitsTo12bits(0xFFFF - (reportBuf[10] | (reportBuf[11] << 8)));
            }
            else
            {
                // Simulate stick data from stick hat data

                int offsetX = 0;
                int offsetY = 0;

                byte stickHat = reportBuf[3];

                // Rotate the stick hat to the correct stick orientation.
                // The following table contains the position of the stick hat for each value
                // Each value on the edges can be easily rotated with a modulo as those are successive increments of 2
                // (1 3 5 7) and (0 2 4 6)
                // ------------------
                // | SL | SYNC | SR |
                // |----------------|
                // | 7  |  0   | 1  |
                // |----------------|
                // | 6  |  8   | 2  |
                // |----------------|
                // | 5  |  4   | 3  |
                // ------------------
                if (stickHat < 0x08) // Some thirdparty controller set it to 0x0F instead of 0x08 when centered
                {
                    var rotation = IsLeft ? 0x02 : 0x06;
                    stickHat = (byte)((stickHat + rotation) % 8);
                }

                switch (stickHat)
                {
                    case 0x00: offsetY = _stickCal[1]; break; // top
                    case 0x01: offsetX = _stickCal[0]; offsetY = _stickCal[1]; break; // top right
                    case 0x02: offsetX = _stickCal[0]; break; // right
                    case 0x03: offsetX = _stickCal[0]; offsetY = -_stickCal[5]; break; // bottom right
                    case 0x04: offsetY = -_stickCal[5]; break; // bottom
                    case 0x05: offsetX = -_stickCal[4]; offsetY = -_stickCal[5]; break; // bottom left
                    case 0x06: offsetX = -_stickCal[4]; break; // left
                    case 0x07: offsetX = -_stickCal[4]; offsetY = _stickCal[1]; break; // top left
                    case 0x08: default: break; // center
                }

                _stickPrecal[0] = (ushort)(_stickCal[2] + offsetX);
                _stickPrecal[1] = (ushort)(_stickCal[3] + offsetY);
            }
        }
        else
        {
            throw new NotImplementedException($"Cannot extract sticks values for report {reportType:X}");
        }
    }

    private void ExtractButtonsValues(ReadOnlySpan<byte> reportBuf)
    {
        byte reportType = reportBuf[0];

        if (reportType == (byte)ReportMode.StandardFull)
        {
            var offset = IsLeft ? 2 : 0;

            if (!IsLeft || IsPro)
            {
                _buttons[(int)Button.B] = (reportBuf[3] & 0x04) != 0;
                _buttons[(int)Button.A] = (reportBuf[3] & 0x08) != 0;
                _buttons[(int)Button.X] = (reportBuf[3] & 0x02) != 0;
                _buttons[(int)Button.Y] = (reportBuf[3] & 0x01) != 0;
            }

            _buttons[(int)Button.DpadDown] = (reportBuf[3 + offset] & (IsLeft ? 0x01 : 0x04)) != 0;
            _buttons[(int)Button.DpadRight] = (reportBuf[3 + offset] & (IsLeft ? 0x04 : 0x08)) != 0;
            _buttons[(int)Button.DpadUp] = (reportBuf[3 + offset] & 0x02) != 0;
            _buttons[(int)Button.DpadLeft] = (reportBuf[3 + offset] & (IsLeft ? 0x08 : 0x01)) != 0;
            _buttons[(int)Button.Home] = (reportBuf[4] & 0x10) != 0;
            _buttons[(int)Button.Capture] = (reportBuf[4] & 0x20) != 0;
            _buttons[(int)Button.Minus] = (reportBuf[4] & 0x01) != 0;
            _buttons[(int)Button.Plus] = (reportBuf[4] & 0x02) != 0;
            _buttons[(int)Button.LS] = (reportBuf[4] & 0x08) != 0;
            _buttons[(int)Button.RS] = (reportBuf[4] & 0x04) != 0;

            if (IsPro)
            {
                _buttons[(int)Button.LB] = (reportBuf[3] & 0x40) != 0;
                _buttons[(int)Button.LT] = (reportBuf[3] & 0x80) != 0;
                _buttons[(int)Button.RB] = (reportBuf[3 + 2] & 0x40) != 0;
                _buttons[(int)Button.RT] = (reportBuf[3 + 2] & 0x80) != 0;
            }
            else
            {
                _buttons[(int)Button.LB] = (reportBuf[3 + offset] & 0x40) != 0;
                _buttons[(int)Button.LT] = (reportBuf[3 + offset] & 0x80) != 0;
                _buttons[(int)Button.SR] = (reportBuf[3 + offset] & 0x10) != 0;
                _buttons[(int)Button.SL] = (reportBuf[3 + offset] & 0x20) != 0;
            }
        }
        else if (reportType == (byte)ReportMode.SimpleHID)
        {
            _buttons[(int)Button.Home] = (reportBuf[2] & 0x10) != 0;
            _buttons[(int)Button.Capture] = (reportBuf[2] & 0x20) != 0;
            _buttons[(int)Button.Minus] = (reportBuf[2] & 0x01) != 0;
            _buttons[(int)Button.Plus] = (reportBuf[2] & 0x02) != 0;
            _buttons[(int)Button.LS] = (reportBuf[2] & 0x04) != 0;
            _buttons[(int)Button.RS] = (reportBuf[2] & 0x08) != 0;

            if (IsPro)
            {
                byte stickHat = reportBuf[3];

                _buttons[(int)Button.DpadDown] = stickHat == 0x03 || stickHat == 0x04 || stickHat == 0x05;
                _buttons[(int)Button.DpadRight] = stickHat == 0x01 || stickHat == 0x02 || stickHat == 0x03;
                _buttons[(int)Button.DpadUp] = stickHat == 0x07 || stickHat == 0x00 || stickHat == 0x01;
                _buttons[(int)Button.DpadLeft] = stickHat == 0x05 || stickHat == 0x06 || stickHat == 0x07;

                _buttons[(int)Button.B] = (reportBuf[1] & 0x01) != 0;
                _buttons[(int)Button.A] = (reportBuf[1] & 0x02) != 0;
                _buttons[(int)Button.X] = (reportBuf[1] & 0x08) != 0;
                _buttons[(int)Button.Y] = (reportBuf[1] & 0x04) != 0;

                _buttons[(int)Button.LB] = (reportBuf[1] & 0x10) != 0;
                _buttons[(int)Button.LT] = (reportBuf[1] & 0x40) != 0;
                _buttons[(int)Button.RB] = (reportBuf[1] & 0x20) != 0;
                _buttons[(int)Button.RT] = (reportBuf[1] & 0x80) != 0;
            }
            else
            {
                _buttons[(int)Button.DpadDown] = (reportBuf[1] & (IsLeft ? 0x02 : 0x04)) != 0;
                _buttons[(int)Button.DpadRight] = (reportBuf[1] & (IsLeft ? 0x08 : 0x01)) != 0;
                _buttons[(int)Button.DpadUp] = (reportBuf[1] & (IsLeft ? 0x04 : 0x02)) != 0;
                _buttons[(int)Button.DpadLeft] = (reportBuf[1] & (IsLeft ? 0x01 : 0x08)) != 0;

                _buttons[(int)Button.LB] = (reportBuf[2] & 0x40) != 0;
                _buttons[(int)Button.LT] = (reportBuf[2] & 0x80) != 0;

                _buttons[(int)Button.SR] = (reportBuf[1] & 0x20) != 0;
                _buttons[(int)Button.SL] = (reportBuf[1] & 0x10) != 0;
            }
        }
        else
        {
            throw new NotImplementedException($"Cannot extract buttons values for report {reportType:X}");
        }
    }

    private void ProcessButtonsAndStick(ReadOnlySpan<byte> reportBuf)
    {
        var activity = false;
        var timestamp = Stopwatch.GetTimestamp();

        if (!IsSNES)
        {
            ExtractSticksValues(reportBuf);

            var cal = _stickCal;
            var dz = _deadzone;
            var range = _range;

            if (_SticksCalibrated)
            {
                cal = _activeStick1;
                dz = _activeStick1Deadzone;
                range = _activeStick1Range;
            }

            CalculateStickCenter(_stickPrecal, cal, dz, range, _stick);

            if (IsPro)
            {
                cal = _stick2Cal;
                dz = _deadzone2;
                range = _range2;

                if (_SticksCalibrated)
                {
                    cal = _activeStick2;
                    dz = _activeStick2Deadzone;
                    range = _activeStick2Range;
                }

                CalculateStickCenter(_stick2Precal, cal, dz, range, _stick2);
            }
            // Read other Joycon's sticks
            else if (IsJoined)
            {
                lock (_otherStick)
                {
                    // Read other stick sent by other joycon
                    if (IsLeft)
                    {
                        Array.Copy(_otherStick, _stick2, 2);
                    }
                    else
                    {
                        _stick = Interlocked.Exchange(ref _stick2, _stick);
                        Array.Copy(_otherStick, _stick, 2);
                    }
                }

                lock (Other._otherStick)
                {
                    // Write stick to linked joycon
                    Array.Copy(IsLeft ? _stick : _stick2, Other._otherStick, 2);
                }
            }
            else
            {
                Array.Clear(_stick2);
            }

            if (_calibrateSticks)
            {
                var sticks = new SticksData(
                    _stickPrecal[0],
                    _stickPrecal[1],
                    _stick2Precal[0],
                    _stick2Precal[1]
                );
                CalibrationStickDatas.Add(sticks);
            }
            else
            {
                //DebugPrint($"X1={_stick[0]:0.00} Y1={_stick[1]:0.00}. X2={_stick2[0]:0.00} Y2={_stick2[1]:0.00}", DebugType.Threading);
            }

            const float stickActivityThreshold = 0.1f;
            if (MathF.Abs(_stick[0]) > stickActivityThreshold ||
                MathF.Abs(_stick[1]) > stickActivityThreshold ||
                MathF.Abs(_stick2[0]) > stickActivityThreshold ||
                MathF.Abs(_stick2[1]) > stickActivityThreshold)
            {
                activity = true;
            }
        }

        // Set button states
        lock (_buttons)
        {
            lock (_buttonsPrev)
            {
                Array.Copy(_buttons, _buttonsPrev, _buttons.Length);
            }
            Array.Clear(_buttons);
            ExtractButtonsValues(reportBuf);
            if (IsJoined)
            {
                if (IsLeft)
                {
                    // Left Joy-Con in joined mode handles D-pad
                    _buttons[(int)Button.DpadDown] = _buttons[(int)Button.DpadDown];
                    _buttons[(int)Button.DpadUp] = _buttons[(int)Button.DpadUp];
                    _buttons[(int)Button.DpadLeft] = _buttons[(int)Button.DpadLeft];
                    _buttons[(int)Button.DpadRight] = _buttons[(int)Button.DpadRight];

                    // Clear face buttons for left Joy-Con
                    _buttons[(int)Button.B] = false;
                    _buttons[(int)Button.A] = false;
                    _buttons[(int)Button.X] = false;
                    _buttons[(int)Button.Y] = false;
                }
                else
                {
                    // Right Joy-Con in joined mode handles face buttons
                    _buttons[(int)Button.B] = _buttons[(int)Button.B];
                    _buttons[(int)Button.A] = _buttons[(int)Button.A];
                    _buttons[(int)Button.X] = _buttons[(int)Button.X];
                    _buttons[(int)Button.Y] = _buttons[(int)Button.Y];

                    // Clear D-pad for right Joy-Con
                    _buttons[(int)Button.DpadDown] = false;
                    _buttons[(int)Button.DpadUp] = false;
                    _buttons[(int)Button.DpadLeft] = false;
                    _buttons[(int)Button.DpadRight] = false;
                }
                _buttons[(int)Button.RT] = _buttons[(int)Button.LT];
                _buttons[(int)Button.RB] = _buttons[(int)Button.LB];


                // Handle shoulder buttons and triggers
                if (IsLeft)
                {
                    _buttons[(int)Button.RB] = Other._buttons[(int)Button.RB];
                    _buttons[(int)Button.RT] = Other._buttons[(int)Button.RT];
                    _buttons[(int)Button.Home] = Other._buttons[(int)Button.Home];
                    _buttons[(int)Button.Plus] = Other._buttons[(int)Button.Plus];
                }
                else
                {
                    _buttons[(int)Button.LB] = Other._buttons[(int)Button.LB];
                    _buttons[(int)Button.LT] = Other._buttons[(int)Button.LT];
                    _buttons[(int)Button.Capture] = Other._buttons[(int)Button.Capture];
                    _buttons[(int)Button.Minus] = Other._buttons[(int)Button.Minus];
                }
            }
            lock (_buttonsUp)
            {
                lock (_buttonsDown)
                {
                    for (var i = 0; i < _buttons.Length; ++i)
                    {
                        _buttonsUp[i] = _buttonsPrev[i] & !_buttons[i];
                        _buttonsDown[i] = !_buttonsPrev[i] & _buttons[i];
                        if (_buttonsPrev[i] != _buttons[i])
                        {
                            _buttonsDownTimestamp[i] = _buttons[i] ? timestamp : -1;
                        }
                        if (_buttonsUp[i] || _buttonsDown[i])
                        {
                            activity = true;
                        }
                    }
                }
            }
        }
        if (activity)
        {
            _timestampActivity = timestamp;
        }
    }

    // Get Gyro/Accel data
    private bool ExtractIMUValues(ReadOnlySpan<byte> reportBuf, int n = 0)
    {
        if (IsSNES || reportBuf[0] != (byte)ReportMode.StandardFull)
        {
            return false;
        }

        _gyrRaw[0] = (short)(reportBuf[19 + n * 12] | (reportBuf[20 + n * 12] << 8));
        _gyrRaw[1] = (short)(reportBuf[21 + n * 12] | (reportBuf[22 + n * 12] << 8));
        _gyrRaw[2] = (short)(reportBuf[23 + n * 12] | (reportBuf[24 + n * 12] << 8));
        _accRaw[0] = (short)(reportBuf[13 + n * 12] | (reportBuf[14 + n * 12] << 8));
        _accRaw[1] = (short)(reportBuf[15 + n * 12] | (reportBuf[16 + n * 12] << 8));
        _accRaw[2] = (short)(reportBuf[17 + n * 12] | (reportBuf[18 + n * 12] << 8));

        if (_calibrateIMU)
        {
            // We need to add the accelerometer offset from the origin position when it's on a flat surface
            short[] accOffset;
            if (IsPro)
            {
                accOffset = _accProHorOffset;
            }
            else if (IsLeft)
            {
                accOffset = _accLeftHorOffset;
            }
            else
            {
                accOffset = _accRightHorOffset;
            }

            var imuData = new IMUData(
                _gyrRaw[0],
                _gyrRaw[1],
                _gyrRaw[2],
                (short)(_accRaw[0] - accOffset[0]),
                (short)(_accRaw[1] - accOffset[1]),
                (short)(_accRaw[2] - accOffset[2])
            );
            CalibrationIMUDatas.Add(imuData);
        }

        var direction = IsLeft ? 1 : -1;

        if (_IMUCalibrated)
        {
            _accG.X = (_accRaw[0] - _activeIMUData[3]) * (1.0f / (_accSensiti[0] - _accNeutral[0])) * 4.0f;
            _gyrG.X = (_gyrRaw[0] - _activeIMUData[0]) * (816.0f / (_gyrSensiti[0] - _activeIMUData[0]));

            _accG.Y = direction * (_accRaw[1] - _activeIMUData[4]) * (1.0f / (_accSensiti[1] - _accNeutral[1])) * 4.0f;
            _gyrG.Y = -direction * (_gyrRaw[1] - _activeIMUData[1]) * (816.0f / (_gyrSensiti[1] - _activeIMUData[1]));

            _accG.Z = direction * (_accRaw[2] - _activeIMUData[5]) * (1.0f / (_accSensiti[2] - _accNeutral[2])) * 4.0f;
            _gyrG.Z = -direction * (_gyrRaw[2] - _activeIMUData[2]) * (816.0f / (_gyrSensiti[2] - _activeIMUData[2]));
        }
        else
        {
            _accG.X = _accRaw[0] * (1.0f / (_accSensiti[0] - _accNeutral[0])) * 4.0f;
            _gyrG.X = (_gyrRaw[0] - _gyrNeutral[0]) * (816.0f / (_gyrSensiti[0] - _gyrNeutral[0]));

            _accG.Y = direction * _accRaw[1] * (1.0f / (_accSensiti[1] - _accNeutral[1])) * 4.0f;
            _gyrG.Y = -direction * (_gyrRaw[1] - _gyrNeutral[1]) * (816.0f / (_gyrSensiti[1] - _gyrNeutral[1]));

            _accG.Z = direction * _accRaw[2] * (1.0f / (_accSensiti[2] - _accNeutral[2])) * 4.0f;
            _gyrG.Z = -direction * (_gyrRaw[2] - _gyrNeutral[2]) * (816.0f / (_gyrSensiti[2] - _gyrNeutral[2]));
        }

        if (IsJoycon && Other == null)
        {
            // single joycon mode; Z do not swap, rest do
            if (IsLeft)
            {
                _accG.X = -_accG.X;
                _accG.Y = -_accG.Y;
                _gyrG.X = -_gyrG.X;
            }
            else
            {
                _gyrG.Y = -_gyrG.Y;
            }

            var temp = _accG.X;
            _accG.X = _accG.Y;
            _accG.Y = -temp;

            temp = _gyrG.X;
            _gyrG.X = _gyrG.Y;
            _gyrG.Y = temp;
        }

        // Update rotation Quaternion
        var degToRad = 0.0174533f;
        _AHRS.Update(
            _gyrG.X * degToRad,
            _gyrG.Y * degToRad,
            _gyrG.Z * degToRad,
            _accG.X,
            _accG.Y,
            _accG.Z
        );

        return true;
    }

    public void Begin()
    {
        if (_receiveReportsThread != null || _sendCommandsThread != null)
        {
            Log("Poll thread cannot start!", Logger.LogLevel.Error);
            return;
        }

        if (_ctsCommunications == null)
        {
            _ctsCommunications = new();
        }

        _receiveReportsThread = new Thread(
            () =>
            {
                try
                {
                    ReceiveReports(_ctsCommunications.Token);
                    Log("Thread receive reports finished.", Logger.LogLevel.Debug);
                }
                catch (OperationCanceledException) when (_ctsCommunications.IsCancellationRequested)
                {
                    Log("Thread receive reports canceled.", Logger.LogLevel.Debug);
                }
                catch (Exception e)
                {
                    Log("Thread receive reports error.", e);
                    throw;
                }
            }
        )
        {
            IsBackground = true
        };

        _sendCommandsThread = new Thread(
            () =>
            {
                try
                {
                    SendCommands(_ctsCommunications.Token);
                    Log("Thread send commands finished.", Logger.LogLevel.Debug);
                }
                catch (OperationCanceledException) when (_ctsCommunications.IsCancellationRequested)
                {
                    Log("Thread send commands canceled.", Logger.LogLevel.Debug);
                }
                catch (Exception e)
                {
                    Log("Thread send commands error.", e);
                    throw;
                }
            }
        )
        {
            IsBackground = true
        };

        _sendCommandsThread.Start();
        Log("Thread send commands started.", Logger.LogLevel.Debug);

        _receiveReportsThread.Start();
        Log("Thread receive reports started.", Logger.LogLevel.Debug);

        Log("Ready.");
    }

    private void CalculateStickCenter(ushort[] vals, ushort[] cal, float deadzone, float range, float[] stick)
    {
        float dx = vals[0] - cal[2];
        float dy = vals[1] - cal[3];

        float normalizedX = dx / (dx > 0 ? cal[0] : cal[4]);
        float normalizedY = dy / (dy > 0 ? cal[1] : cal[5]);

        float magnitude = MathF.Sqrt(normalizedX * normalizedX + normalizedY * normalizedY);

        if (magnitude <= deadzone || range <= deadzone)
        {
            // Inner deadzone
            stick[0] = 0.0f;
            stick[1] = 0.0f;
        }
        else
        {
            float normalizedMagnitude = Math.Min(1.0f, (magnitude - deadzone) / (range - deadzone));
            float scale = normalizedMagnitude / magnitude;

            normalizedX *= scale;
            normalizedY *= scale;

            if (!Config.SticksSquared || normalizedX == 0f || normalizedY == 0f)
            {
                stick[0] = normalizedX;
                stick[1] = normalizedY;
            }
            else
            {
                // Expand the circle to a square area
                if (Math.Abs(normalizedX) > Math.Abs(normalizedY))
                {
                    stick[0] = Math.Sign(normalizedX) * normalizedMagnitude;
                    stick[1] = stick[0] * normalizedY / normalizedX;
                }
                else
                {
                    stick[1] = Math.Sign(normalizedY) * normalizedMagnitude;
                    stick[0] = stick[1] * normalizedX / normalizedY;
                }
            }

            stick[0] = Math.Clamp(stick[0], -1.0f, 1.0f);
            stick[1] = Math.Clamp(stick[1], -1.0f, 1.0f);
        }
    }

    private static short CastStickValue(float stickValue)
    {
        return (short)MathF.Round(stickValue * (stickValue > 0 ? short.MaxValue : -short.MinValue));
    }

    private static byte CastStickValueByte(float stickValue)
    {
        return (byte)MathF.Round((stickValue + 1.0f) * 0.5F * byte.MaxValue);
    }

    public void SetRumble(float lowFreq, float highFreq, float amp)
    {
        if (State <= Status.Attached)
        {
            return;
        }

        _rumbles.Enqueue(lowFreq, highFreq, amp);
    }

    // Run from poll thread
    private void SendRumble(Span<byte> buf, ReadOnlySpan<byte> data)
    {
        buf.Clear();

        buf[0] = 0x10;
        buf[1] = (byte)(_globalCount & 0x0F);
        ++_globalCount;

        data.Slice(0, 8).CopyTo(buf.Slice(2));
        PrintArray<byte>(buf, DebugType.Rumble, 10, format: "Rumble data sent: {0:S}");
        Write(buf);
    }

    private bool Subcommand(byte sc, ReadOnlySpan<byte> bufParameters, bool print = true)
    {
        if (_handle == IntPtr.Zero)
        {
            return false;
        }

        Span<byte> buf = stackalloc byte[_CommandLength];
        buf.Clear();

        _defaultBuf.AsSpan(0, 8).CopyTo(buf.Slice(2));
        bufParameters.CopyTo(buf.Slice(11));
        buf[10] = sc;
        buf[1] = (byte)(_globalCount & 0x0F);
        buf[0] = 0x01;
        ++_globalCount;

        if (print)
        {
            PrintArray<byte>(buf, DebugType.Comms, bufParameters.Length, 11, $"Subcommand {sc:X2} sent." + " Data: {0:S}");
        }

        int length = Write(buf);

        return length > 0;
    }

    private int SubcommandCheck(byte sc, ReadOnlySpan<byte> bufParameters, bool print = true)
    {
        Span<byte> response = stackalloc byte[ReportLength];

        return SubcommandCheck(sc, bufParameters, response, print);
    }

    private int SubcommandCheck(byte sc, ReadOnlySpan<byte> bufParameters, Span<byte> response, bool print = true)
    {
        bool sent = Subcommand(sc, bufParameters, print);
        if (!sent)
        {
            DebugPrint($"Subcommand write error: {ErrorMessage()}", DebugType.Comms);
            return 0;
        }

        int tries = 0;
        int length;
        bool responseFound;
        do
        {
            length = Read(response, 100); // don't set the timeout lower than 100 or might not always work
            responseFound = length >= 20 && response[0] == 0x21 && response[14] == sc;

            if (length < 0)
            {
                DebugPrint($"Subcommand read error: {ErrorMessage()}", DebugType.Comms);
            }

            tries++;
        } while (tries < 10 && !responseFound && length >= 0);

        if (!responseFound)
        {
            DebugPrint("No response.", DebugType.Comms);
            return 0;
        }

        if (print)
        {
            PrintArray<byte>(
                response,
                DebugType.Comms,
                length - 1,
                1,
                $"Response ID {response[0]:X2}." + " Data: {0:S}"
            );
        }

        return length;
    }

    private float CalculateDeadzone(ushort[] cal, ushort deadzone)
    {
        return 2.0f * deadzone / Math.Max(cal[0] + cal[4], cal[1] + cal[5]);
    }

    private float CalculateRange(ushort range)
    {
        return (float)range / 0xFFF;
    }

    private bool CalibrationDataSupported()
    {
        return !IsSNES && !IsThirdParty;
    }

    private bool DumpCalibrationData()
    {
        if (!CalibrationDataSupported())
        {
            // Use default joycon values for sensors
            Array.Fill(_accSensiti, (short)16384);
            Array.Fill(_accNeutral, (short)0);
            Array.Fill(_gyrSensiti, (short)13371);
            Array.Fill(_gyrNeutral, (short)0);

            // Default stick calibration
            Array.Fill(_stickCal, (ushort)2048);
            Array.Fill(_stick2Cal, (ushort)2048);

            _deadzone = Config.DefaultDeadzone;
            _deadzone2 = Config.DefaultDeadzone;

            _range = Config.DefaultRange;
            _range2 = Config.DefaultRange;

            _DumpedCalibration = false;

            return true;
        }

        var ok = true;

        // get user calibration data if possible

        // Sticks axis
        {
            var userStickData = ReadSPICheck(0x80, 0x10, 0x16, ref ok);
            var factoryStickData = ReadSPICheck(0x60, 0x3D, 0x12, ref ok);

            var stick1Data = new ReadOnlySpan<byte>(userStickData, IsLeft ? 2 : 13, 9);
            var stick1Name = IsLeft ? "left" : "right";

            if (ok)
            {
                if (userStickData[IsLeft ? 0 : 11] == 0xB2 && userStickData[IsLeft ? 1 : 12] == 0xA1)
                {
                    DebugPrint($"Retrieve user {stick1Name} stick calibration data.", DebugType.Comms);
                }
                else
                {
                    stick1Data = new ReadOnlySpan<byte>(factoryStickData, IsLeft ? 0 : 9, 9);

                    DebugPrint($"Retrieve factory {stick1Name} stick calibration data.", DebugType.Comms);
                }
            }

            _stickCal[IsLeft ? 0 : 2] = (ushort)(((stick1Data[1] << 8) & 0xF00) | stick1Data[0]); // X Axis Max above center
            _stickCal[IsLeft ? 1 : 3] = (ushort)((stick1Data[2] << 4) | (stick1Data[1] >> 4)); // Y Axis Max above center
            _stickCal[IsLeft ? 2 : 4] = (ushort)(((stick1Data[4] << 8) & 0xF00) | stick1Data[3]); // X Axis Center
            _stickCal[IsLeft ? 3 : 5] = (ushort)((stick1Data[5] << 4) | (stick1Data[4] >> 4)); // Y Axis Center
            _stickCal[IsLeft ? 4 : 0] = (ushort)(((stick1Data[7] << 8) & 0xF00) | stick1Data[6]); // X Axis Min below center
            _stickCal[IsLeft ? 5 : 1] = (ushort)((stick1Data[8] << 4) | (stick1Data[7] >> 4)); // Y Axis Min below center

            PrintArray<ushort>(_stickCal, len: 6, start: 0, format: $"{stick1Name} stick 1 calibration data: {{0:S}}");

            if (IsPro)
            {
                var stick2Data = new ReadOnlySpan<byte>(userStickData, !IsLeft ? 2 : 13, 9);
                var stick2Name = !IsLeft ? "left" : "right";

                if (ok)
                {
                    if (userStickData[!IsLeft ? 0 : 11] == 0xB2 && userStickData[!IsLeft ? 1 : 12] == 0xA1)
                    {
                        DebugPrint($"Retrieve user {stick2Name} stick calibration data.", DebugType.Comms);
                    }
                    else
                    {
                        stick2Data = new ReadOnlySpan<byte>(factoryStickData, !IsLeft ? 0 : 9, 9);

                        DebugPrint($"Retrieve factory {stick2Name} stick calibration data.", DebugType.Comms);
                    }
                }

                _stick2Cal[!IsLeft ? 0 : 2] = (ushort)(((stick2Data[1] << 8) & 0xF00) | stick2Data[0]); // X Axis Max above center
                _stick2Cal[!IsLeft ? 1 : 3] = (ushort)((stick2Data[2] << 4) | (stick2Data[1] >> 4)); // Y Axis Max above center
                _stick2Cal[!IsLeft ? 2 : 4] = (ushort)(((stick2Data[4] << 8) & 0xF00) | stick2Data[3]); // X Axis Center
                _stick2Cal[!IsLeft ? 3 : 5] = (ushort)((stick2Data[5] << 4) | (stick2Data[4] >> 4)); // Y Axis Center
                _stick2Cal[!IsLeft ? 4 : 0] = (ushort)(((stick2Data[7] << 8) & 0xF00) | stick2Data[6]); // X Axis Min below center
                _stick2Cal[!IsLeft ? 5 : 1] = (ushort)((stick2Data[8] << 4) | (stick2Data[7] >> 4)); // Y Axis Min below center

                PrintArray<ushort>(_stick2Cal, len: 6, start: 0, format: $"{stick2Name} stick calibration data: {{0:S}}");
            }
        }

        // Sticks deadzones and ranges
        // Looks like the range is a 12 bits precision ratio.
        // I suppose the right way to interpret it is as a float by dividing it by 0xFFF
        {
            var factoryDeadzoneData = ReadSPICheck(0x60, IsLeft ? (byte)0x86 : (byte)0x98, 6, ref ok);

            var deadzone = (ushort)(((factoryDeadzoneData[4] << 8) & 0xF00) | factoryDeadzoneData[3]);
            _deadzone = CalculateDeadzone(_stickCal, deadzone);

            var range = (ushort)((factoryDeadzoneData[5] << 4) | (factoryDeadzoneData[4] >> 4));
            _range = CalculateRange(range);

            if (IsPro)
            {
                var factoryDeadzone2Data = ReadSPICheck(0x60, !IsLeft ? (byte)0x86 : (byte)0x98, 6, ref ok);

                var deadzone2 = (ushort)(((factoryDeadzone2Data[4] << 8) & 0xF00) | factoryDeadzone2Data[3]);
                _deadzone2 = CalculateDeadzone(_stick2Cal, deadzone2);

                var range2 = (ushort)((factoryDeadzone2Data[5] << 4) | (factoryDeadzone2Data[4] >> 4));
                _range2 = CalculateRange(range2);
            }
        }

        // Gyro and accelerometer
        {
            var userSensorData = ReadSPICheck(0x80, 0x26, 0x1A, ref ok);
            ReadOnlySpan<byte> sensorData = new ReadOnlySpan<byte>(userSensorData, 2, 24);

            if (ok)
            {
                if (userSensorData[0] == 0xB2 && userSensorData[1] == 0xA1)
                {
                    DebugPrint($"Retrieve user sensors calibration data.", DebugType.Comms);
                }
                else
                {
                    var factorySensorData = ReadSPICheck(0x60, 0x20, 0x18, ref ok);
                    sensorData = new ReadOnlySpan<byte>(factorySensorData, 0, 24);

                    DebugPrint($"Retrieve factory sensors calibration data.", DebugType.Comms);
                }
            }

            _accNeutral[0] = (short)(sensorData[0] | (sensorData[1] << 8));
            _accNeutral[1] = (short)(sensorData[2] | (sensorData[3] << 8));
            _accNeutral[2] = (short)(sensorData[4] | (sensorData[5] << 8));

            _accSensiti[0] = (short)(sensorData[6] | (sensorData[7] << 8));
            _accSensiti[1] = (short)(sensorData[8] | (sensorData[9] << 8));
            _accSensiti[2] = (short)(sensorData[10] | (sensorData[11] << 8));

            _gyrNeutral[0] = (short)(sensorData[12] | (sensorData[13] << 8));
            _gyrNeutral[1] = (short)(sensorData[14] | (sensorData[15] << 8));
            _gyrNeutral[2] = (short)(sensorData[16] | (sensorData[17] << 8));

            _gyrSensiti[0] = (short)(sensorData[18] | (sensorData[19] << 8));
            _gyrSensiti[1] = (short)(sensorData[20] | (sensorData[21] << 8));
            _gyrSensiti[2] = (short)(sensorData[22] | (sensorData[23] << 8));

            bool noCalibration = false;

            if (_accNeutral[0] == -1 || _accNeutral[1] == -1 || _accNeutral[2] == -1)
            {
                Array.Fill(_accNeutral, (short)0);
                noCalibration = true;
            }

            if (_accSensiti[0] == -1 || _accSensiti[1] == -1 || _accSensiti[2] == -1)
            {
                // Default accelerometer sensitivity for joycons
                Array.Fill(_accSensiti, (short)16384);
                noCalibration = true;
            }

            if (_gyrNeutral[0] == -1 || _gyrNeutral[1] == -1 || _gyrNeutral[2] == -1)
            {
                Array.Fill(_gyrNeutral, (short)0);
                noCalibration = true;
            }

            if (_gyrSensiti[0] == -1 || _gyrSensiti[1] == -1 || _gyrSensiti[2] == -1)
            {
                // Default gyroscope sensitivity for joycons
                Array.Fill(_gyrSensiti, (short)13371);
                noCalibration = true;
            }

            if (noCalibration)
            {
                Log($"Some sensor calibrations datas are missing, fallback to default ones.", Logger.LogLevel.Warning);
            }

            PrintArray<short>(_gyrNeutral, len: 3, d: DebugType.IMU, format: "Gyro neutral position: {0:S}");
        }

        if (!ok)
        {
            Log("Error while reading calibration datas.", Logger.LogLevel.Error);
        }

        _DumpedCalibration = ok;

        return ok;
    }

    public void SetCalibration(bool userCalibration)
    {
        if (userCalibration)
        {
            GetActiveIMUData();
            GetActiveSticksData();
        }
        else
        {
            _IMUCalibrated = false;
            _SticksCalibrated = false;
        }

        var calibrationType = _SticksCalibrated ? "user" : _DumpedCalibration ? "controller" : "default";
        Log($"Using {calibrationType} sticks calibration.");

        calibrationType = _IMUCalibrated ? "user" : _DumpedCalibration ? "controller" : "default";
        Log($"Using {calibrationType} sensors calibration.");
    }

    private int Read(Span<byte> response, int timeout = 100)
    {
        if (response.Length < ReportLength)
        {
            throw new IndexOutOfRangeException();
        }

        if (IsDeviceError)
        {
            return DeviceErroredCode;
        }

        if (timeout >= 0)
        {
            return HIDApi.ReadTimeout(_handle, response, ReportLength, timeout);
        }
        return HIDApi.Read(_handle, response, ReportLength);
    }

    private int Write(ReadOnlySpan<byte> command)
    {
        if (command.Length < _CommandLength)
        {
            throw new IndexOutOfRangeException();
        }

        if (IsDeviceError)
        {
            return DeviceErroredCode;
        }

        int length = HIDApi.Write(_handle, command, _CommandLength);
        return length;
    }

    private string ErrorMessage()
    {
        if (IsDeviceError)
        {
            return $"Device unavailable : {State}";
        }
        return HIDApi.Error(_handle);
    }

    private bool USBCommand(byte command, bool print = true)
    {
        if (_handle == IntPtr.Zero)
        {
            return false;
        }

        Span<byte> buf = stackalloc byte[_CommandLength];
        buf.Clear();

        buf[0] = 0x80;
        buf[1] = command;

        if (print)
        {
            DebugPrint($"USB command {command:X2} sent.", DebugType.Comms);
        }

        int length = Write(buf);

        return length > 0;
    }

    private int USBCommandCheck(byte command, bool print = true)
    {
        Span<byte> response = stackalloc byte[ReportLength];

        return USBCommandCheck(command, response, print);
    }

    private int USBCommandCheck(byte command, Span<byte> response, bool print = true)
    {
        if (!USBCommand(command, print))
        {
            DebugPrint($"USB command write error: {ErrorMessage()}", DebugType.Comms);
            return 0;
        }

        int tries = 0;
        int length;
        bool responseFound;

        do
        {
            length = Read(response, 100);
            responseFound = length > 1 && response[0] == 0x81 && response[1] == command;

            if (length < 0)
            {
                DebugPrint($"USB command read error: {ErrorMessage()}", DebugType.Comms);
            }

            ++tries;
        } while (tries < 10 && !responseFound && length >= 0);

        if (!responseFound)
        {
            DebugPrint("No USB response.", DebugType.Comms);
            return 0;
        }

        if (print)
        {
            PrintArray<byte>(
                response,
                DebugType.Comms,
                length - 1,
                1,
                $"USB response ID {response[0]:X2}." + " Data: {0:S}"
            );
        }

        return length;
    }

    private byte[] ReadSPICheck(byte addr1, byte addr2, int len, ref bool ok, bool print = false)
    {
        var readBuf = new byte[len];
        if (!ok)
        {
            return readBuf;
        }

        byte[] bufSubcommand = { addr2, addr1, 0x00, 0x00, (byte)len };

        Span<byte> response = stackalloc byte[ReportLength];

        ok = false;
        for (var i = 0; i < 5; ++i)
        {
            int length = SubcommandCheck(0x10, bufSubcommand, response, false);
            if (length >= 20 + len && response[15] == addr2 && response[16] == addr1)
            {
                ok = true;
                break;
            }
        }

        if (ok)
        {
            response.Slice(20, len).CopyTo(readBuf);
            if (print)
            {
                PrintArray<byte>(readBuf, DebugType.Comms, len);
            }
        }
        else
        {
            Log("ReadSPI error.", Logger.LogLevel.Error);
        }

        return readBuf;
    }

    private void PrintArray<T>(
        ReadOnlySpan<T> arr,
        DebugType d = DebugType.None,
        int len = 0,
        int start = 0,
        string format = "{0:S}"
    )
    {
        if (d != Config.DebugType && Config.DebugType != DebugType.All)
        {
            return;
        }

        if (len == 0)
        {
            len = arr.Length;
        }

        var tostr = "";
        for (var i = 0; i < len; ++i)
        {
            tostr += string.Format(
                arr[0] is byte ? "{0:X2} " : arr[0] is float ? "{0:F} " : "{0:D} ",
                arr[i + start]
            );
        }

        DebugPrint(string.Format(format, tostr), d);
    }

    public class StateChangedEventArgs : EventArgs
    {
        public Status State { get; }

        public StateChangedEventArgs(Status state)
        {
            State = state;
        }
    }

    public static DpadDirection GetDirection(bool up, bool down, bool left, bool right)
    {
        // Avoid conflicting outputs
        if (up && down)
        {
            up = false;
            down = false;
        }

        if (left && right)
        {
            left = false;
            right = false;
        }

        if (up)
        {
            if (left) return DpadDirection.Northwest;
            if (right) return DpadDirection.Northeast;
            return DpadDirection.North;
        }

        if (down)
        {
            if (left) return DpadDirection.Southwest;
            if (right) return DpadDirection.Southeast;
            return DpadDirection.South;
        }

        if (left)
        {
            return DpadDirection.West;
        }

        if (right)
        {
            return DpadDirection.East;
        }

        return DpadDirection.None;
    }

    private static OutputControllerXbox360InputState MapToXbox360Input(Joycon input)
    {
        var output = new OutputControllerXbox360InputState();

        var isPro = input.IsPro;
        var isLeft = input.IsLeft;
        var isSNES = input.IsSNES;
        var other = input.Other;

        var buttons = input._buttonsRemapped;
        var stick = input._stick;
        var stick2 = input._stick2;
        var sliderVal = input._sliderVal;

        var gyroAnalogSliders = input.Config.GyroAnalogSliders;
        var swapAB = input.Config.SwapAB;
        var swapXY = input.Config.SwapXY;

        if (other != null && !isLeft)
        {
            gyroAnalogSliders = other.Config.GyroAnalogSliders;
            swapAB = other.Config.SwapAB;
            swapXY = other.Config.SwapXY;
        }

        if (isPro)
        {
            // Pro controller mapping
            output.A = buttons[(int)(!swapAB ? Button.B : Button.A)];
            output.B = buttons[(int)(!swapAB ? Button.A : Button.B)];
            output.X = buttons[(int)(!swapXY ? Button.Y : Button.X)];
            output.Y = buttons[(int)(!swapXY ? Button.X : Button.Y)];

            output.DpadUp = buttons[(int)Button.DpadUp];
            output.DpadDown = buttons[(int)Button.DpadDown];
            output.DpadLeft = buttons[(int)Button.DpadLeft];
            output.DpadRight = buttons[(int)Button.DpadRight];

            output.Back = buttons[(int)Button.Minus];
            output.Start = buttons[(int)Button.Plus];
            output.Guide = buttons[(int)Button.Home];

            output.ShoulderLeft = buttons[(int)Button.LB];
            output.ShoulderRight = buttons[(int)Button.RB];

            output.ThumbStickLeft = buttons[(int)Button.LS];
            output.ThumbStickRight = buttons[(int)Button.RS];
        }
        else if (other != null) // Joined Joy-Cons
        {
            if (isLeft)
            {
                // Left Joy-Con handles D-pad
                output.DpadUp = buttons[(int)Button.DpadUp];
                output.DpadDown = buttons[(int)Button.DpadDown];
                output.DpadLeft = buttons[(int)Button.DpadLeft];
                output.DpadRight = buttons[(int)Button.DpadRight];


                // Face buttons come from the right Joy-Con
                output.A = other._buttonsRemapped[(int)(!swapAB ? Button.B : Button.A)];
                output.B = other._buttonsRemapped[(int)(!swapAB ? Button.A : Button.B)];
                output.X = other._buttonsRemapped[(int)(!swapXY ? Button.Y : Button.X)];
                output.Y = other._buttonsRemapped[(int)(!swapXY ? Button.X : Button.Y)];

                output.ShoulderLeft = buttons[(int)Button.LB];
                output.ShoulderRight = other._buttonsRemapped[(int)Button.RB];

                output.Back = buttons[(int)Button.Minus];
                output.Start = other._buttonsRemapped[(int)Button.Plus];
                output.Guide = buttons[(int)Button.Home];

                output.ThumbStickLeft = buttons[(int)Button.LS];
                output.ThumbStickRight = other._buttonsRemapped[(int)Button.RS];
            }
            else
            {
                // Right Joy-Con handles face buttons
                output.A = buttons[(int)(!swapAB ? Button.B : Button.A)];
                output.B = buttons[(int)(!swapAB ? Button.A : Button.B)];
                output.X = buttons[(int)(!swapXY ? Button.Y : Button.X)];
                output.Y = buttons[(int)(!swapXY ? Button.X : Button.Y)];

                // D-pad comes from the left Joy-Con
                output.DpadUp = other._buttonsRemapped[(int)Button.DpadUp];
                output.DpadDown = other._buttonsRemapped[(int)Button.DpadDown];
                output.DpadLeft = other._buttonsRemapped[(int)Button.DpadLeft];
                output.DpadRight = other._buttonsRemapped[(int)Button.DpadRight];

                output.ThumbStickLeft = buttons[(int)Button.LS];

                output.ShoulderLeft = other._buttonsRemapped[(int)Button.LB];
                output.ShoulderRight = buttons[(int)Button.RB];

                output.Back = other._buttonsRemapped[(int)Button.Minus];
                output.Start = buttons[(int)Button.Plus];
                output.Guide = other._buttonsRemapped[(int)Button.Home];

                output.ThumbStickLeft = other._buttonsRemapped[(int)Button.LS];
                output.ThumbStickRight = buttons[(int)Button.RS];
            }
        }
        else // Single Joy-Con mode
        {
            if (isLeft)
            {
                // Left Joy-Con in single mode
                output.DpadUp = buttons[(int)Button.DpadUp];
                output.DpadDown = buttons[(int)Button.DpadDown];
                output.DpadLeft = buttons[(int)Button.DpadLeft];
                output.DpadRight = buttons[(int)Button.DpadRight];

                // Map SL and SR to A and B
                output.A = buttons[(int)Button.SR];
                output.B = buttons[(int)Button.SL];

                output.ShoulderLeft = buttons[(int)Button.LB];
                output.ShoulderRight = buttons[(int)Button.RB];
            }
            else
            {
                // Right Joy-Con in single mode
                output.A = buttons[(int)(!swapAB ? Button.B : Button.A)];
                output.B = buttons[(int)(!swapAB ? Button.A : Button.B)];
                output.X = buttons[(int)(!swapXY ? Button.Y : Button.X)];
                output.Y = buttons[(int)(!swapXY ? Button.X : Button.Y)];

                // Map SL and SR to D-pad Left and Right
                output.DpadLeft = buttons[(int)Button.SL];
                output.DpadRight = buttons[(int)Button.SR];

                output.ShoulderLeft = buttons[(int)Button.LB];
                output.ShoulderRight = buttons[(int)Button.RB];
            }

            output.Back = buttons[(int)Button.Minus];
            output.Start = buttons[(int)Button.Plus];
            output.Guide = buttons[(int)Button.Home];

            output.ThumbStickLeft = buttons[(int)Button.LS];
            output.ThumbStickRight = buttons[(int)Button.RS];
        }

        // Handle analog sticks
        if (!isSNES)
        {
            if (other != null || isPro)
            {
                output.AxisLeftX = CastStickValue(other == input && !isLeft ? stick2[0] : stick[0]);
                output.AxisLeftY = CastStickValue(other == input && !isLeft ? stick2[1] : stick[1]);
                output.AxisRightX = CastStickValue(other == input && !isLeft ? stick[0] : stick2[0]);
                output.AxisRightY = CastStickValue(other == input && !isLeft ? stick[1] : stick2[1]);
            }
            else
            {
                // Single Joy-Con mode
                output.AxisLeftY = CastStickValue((isLeft ? 1 : -1) * stick[0]);
                output.AxisLeftX = CastStickValue((isLeft ? -1 : 1) * stick[1]);
            }
        }

        // Handle triggers
        if (isPro || other != null)
        {
            var lval = gyroAnalogSliders ? sliderVal[0] : byte.MaxValue;
            var rval = gyroAnalogSliders ? sliderVal[1] : byte.MaxValue;
            output.TriggerLeft = (byte)(buttons[(int)Button.LT] ? lval : 0);
            output.TriggerRight = (byte)(buttons[(int)Button.RT] ? rval : 0);
        }
        else
        {
            // Single Joy-Con mode
            if (isLeft)
            {
                output.TriggerLeft = (byte)(buttons[(int)Button.LT] ? byte.MaxValue : 0);
                output.TriggerRight = (byte)(buttons[(int)Button.LB] ? byte.MaxValue : 0);
            }
            else
            {
                output.TriggerLeft = (byte)(buttons[(int)Button.LB] ? byte.MaxValue : 0);
                output.TriggerRight = (byte)(buttons[(int)Button.LT] ? byte.MaxValue : 0);
            }
        }

        return output;
    }

    public static OutputControllerDualShock4InputState MapToDualShock4Input(Joycon input)
    {
        var output = new OutputControllerDualShock4InputState();

        var isPro = input.IsPro;
        var isLeft = input.IsLeft;
        var isSNES = input.IsSNES;
        var other = input.Other;

        var buttons = input._buttonsRemapped;
        var stick = input._stick;
        var stick2 = input._stick2;
        var sliderVal = input._sliderVal;

        var gyroAnalogSliders = input.Config.GyroAnalogSliders;
        var swapAB = input.Config.SwapAB;
        var swapXY = input.Config.SwapXY;

        if (other != null && !isLeft)
        {
            gyroAnalogSliders = other.Config.GyroAnalogSliders;
            swapAB = other.Config.SwapAB;
            swapXY = other.Config.SwapXY;
        }

        if (isPro)
        {
            output.Cross = buttons[(int)(!swapAB ? Button.B : Button.A)];
            output.Circle = buttons[(int)(!swapAB ? Button.A : Button.B)];
            output.Triangle = buttons[(int)(!swapXY ? Button.X : Button.Y)];
            output.Square = buttons[(int)(!swapXY ? Button.Y : Button.X)];

            output.DPad = GetDirection(
                buttons[(int)Button.DpadUp],
                buttons[(int)Button.DpadDown],
                buttons[(int)Button.DpadLeft],
                buttons[(int)Button.DpadRight]
            );

            output.Share = buttons[(int)Button.Capture];
            output.Options = buttons[(int)Button.Plus];
            output.Ps = buttons[(int)Button.Home];
            output.Touchpad = buttons[(int)Button.Minus];
            output.ShoulderLeft = buttons[(int)Button.LB];
            output.ShoulderRight = buttons[(int)Button.RB];
            output.ThumbLeft = buttons[(int)Button.LS];
            output.ThumbRight = buttons[(int)Button.RS];
        }
        else
        {
            if (other != null)
            {
                // no need for && other != this
                output.Cross = !swapAB
                        ? buttons[(int)(isLeft ? Button.B : Button.DpadDown)]
                        : buttons[(int)(isLeft ? Button.A : Button.DpadRight)];
                output.Circle = swapAB
                        ? buttons[(int)(isLeft ? Button.B : Button.DpadDown)]
                        : buttons[(int)(isLeft ? Button.A : Button.DpadRight)];
                output.Triangle = !swapXY
                        ? buttons[(int)(isLeft ? Button.X : Button.DpadUp)]
                        : buttons[(int)(isLeft ? Button.Y : Button.DpadLeft)];
                output.Square = swapXY
                        ? buttons[(int)(isLeft ? Button.X : Button.DpadUp)]
                        : buttons[(int)(isLeft ? Button.Y : Button.DpadLeft)];

                output.DPad = GetDirection(
                    buttons[(int)(isLeft ? Button.DpadUp : Button.X)],
                    buttons[(int)(isLeft ? Button.DpadDown : Button.B)],
                    buttons[(int)(isLeft ? Button.DpadLeft : Button.Y)],
                    buttons[(int)(isLeft ? Button.DpadRight : Button.A)]
                );

                output.Share = buttons[(int)Button.Capture];
                output.Options = buttons[(int)Button.Plus];
                output.Ps = buttons[(int)Button.Home];
                output.Touchpad = buttons[(int)Button.Minus];
                output.ShoulderLeft = buttons[(int)(isLeft ? Button.LB : Button.RB)];
                output.ShoulderRight = buttons[(int)(isLeft ? Button.RB : Button.LB)];
                output.ThumbLeft = buttons[(int)(isLeft ? Button.LS : Button.RS)];
                output.ThumbRight = buttons[(int)(isLeft ? Button.RS : Button.LS)];
            }
            else
            {
                // single joycon mode
                output.Cross = !swapAB
                        ? buttons[(int)(isLeft ? Button.DpadLeft : Button.DpadRight)]
                        : buttons[(int)(isLeft ? Button.DpadDown : Button.DpadUp)];
                output.Circle = swapAB
                        ? buttons[(int)(isLeft ? Button.DpadLeft : Button.DpadRight)]
                        : buttons[(int)(isLeft ? Button.DpadDown : Button.DpadUp)];
                output.Triangle = !swapXY
                        ? buttons[(int)(isLeft ? Button.DpadRight : Button.DpadLeft)]
                        : buttons[(int)(isLeft ? Button.DpadUp : Button.DpadDown)];
                output.Square = swapXY
                        ? buttons[(int)(isLeft ? Button.DpadRight : Button.DpadLeft)]
                        : buttons[(int)(isLeft ? Button.DpadUp : Button.DpadDown)];

                output.Ps = buttons[(int)Button.Minus] | buttons[(int)Button.Home];
                output.Options = buttons[(int)Button.Plus] | buttons[(int)Button.Capture];

                output.ShoulderLeft = buttons[(int)Button.SL];
                output.ShoulderRight = buttons[(int)Button.SR];

                output.ThumbLeft = buttons[(int)Button.LS];
            }
        }

        if (!isSNES)
        {
            if (other != null || isPro)
            {
                // no need for && other != this
                output.ThumbLeftX = CastStickValueByte(other == input && !isLeft ? stick2[0] : stick[0]);
                output.ThumbLeftY = CastStickValueByte(other == input && !isLeft ? -stick2[1] : -stick[1]);
                output.ThumbRightX = CastStickValueByte(other == input && !isLeft ? stick[0] : stick2[0]);
                output.ThumbRightY = CastStickValueByte(other == input && !isLeft ? -stick[1] : -stick2[1]);

                //input.DebugPrint($"X:{-stick[0]:0.00} Y:{stick[1]:0.00}", DebugType.Threading);
                //input.DebugPrint($"X:{output.ThumbLeftX} Y:{output.ThumbLeftY}", DebugType.Threading);
            }
            else
            {
                // single joycon mode
                output.ThumbLeftY = CastStickValueByte((isLeft ? 1 : -1) * -stick[0]);
                output.ThumbLeftX = CastStickValueByte((isLeft ? 1 : -1) * -stick[1]);
            }
        }

        if (isPro || other != null)
        {
            var lval = gyroAnalogSliders ? sliderVal[0] : byte.MaxValue;
            var rval = gyroAnalogSliders ? sliderVal[1] : byte.MaxValue;
            output.TriggerLeftValue = (byte)(buttons[(int)(isLeft ? Button.LT : Button.RT)] ? lval : 0);
            output.TriggerRightValue = (byte)(buttons[(int)(isLeft ? Button.RT : Button.LT)] ? rval : 0);
        }
        else
        {
            output.TriggerLeftValue = (byte)(buttons[(int)(isLeft ? Button.LT : Button.LB)] ? byte.MaxValue : 0);
            output.TriggerRightValue = (byte)(buttons[(int)(isLeft ? Button.LB : Button.LT)] ? byte.MaxValue : 0);
        }

        // Output digital L2 / R2 in addition to analog L2 / R2
        output.TriggerLeft = output.TriggerLeftValue > 0;
        output.TriggerRight = output.TriggerRightValue > 0;

        return output;
    }

    public static string GetControllerName(ControllerType type)
    {
        return type switch
        {
            ControllerType.JoyconLeft => "Left joycon",
            ControllerType.JoyconRight => "Right joycon",
            ControllerType.Pro => "Pro controller",
            ControllerType.SNES => "SNES controller",
            _ => "Controller"
        };
    }

    public string GetControllerName()
    {
        return GetControllerName(Type);
    }

    public void StartSticksCalibration()
    {
        CalibrationStickDatas.Clear();
        _calibrateSticks = true;
    }

    public void StopSticksCalibration(bool clean = false)
    {
        _calibrateSticks = false;

        if (clean)
        {
            CalibrationStickDatas.Clear();
        }
    }

    public void StartIMUCalibration()
    {
        CalibrationIMUDatas.Clear();
        _calibrateIMU = true;
    }

    public void StopIMUCalibration(bool clean = false)
    {
        _calibrateIMU = false;

        if (clean)
        {
            CalibrationIMUDatas.Clear();
        }
    }

    private void Log(string message, Logger.LogLevel level = Logger.LogLevel.Info, DebugType type = DebugType.None)
    {
        if (level == Logger.LogLevel.Debug && type != DebugType.None)
        {
            _form.Log($"[P{PadId + 1}] [{type.ToString().ToUpper()}] {message}", level);
        }
        else
        {
            _form.Log($"[P{PadId + 1}] {message}", level);
        }
    }

    private void Log(string message, Exception e, Logger.LogLevel level = Logger.LogLevel.Error)
    {
        _form.Log($"[P{PadId + 1}] {message}", e, level);
    }

    public void ApplyConfig(bool showErrors = true)
    {
        var oldConfig = Config.Clone();
        Config.ShowErrors = showErrors;
        Config.Update();

        if (oldConfig.ShowAsXInput != Config.ShowAsXInput)
        {
            if (Config.ShowAsXInput)
            {
                OutXbox.Connect();
            }
            else
            {
                OutXbox.Disconnect();
            }
        }

        if (oldConfig.ShowAsDs4 != Config.ShowAsDs4)
        {
            if (Config.ShowAsDs4)
            {
                OutDs4.Connect();
            }
            else
            {
                OutDs4.Disconnect();
            }
        }

        if (oldConfig.HomeLEDOn != Config.HomeLEDOn)
        {
            SetHomeLight(Config.HomeLEDOn);
        }

        if (oldConfig.DefaultDeadzone != Config.DefaultDeadzone)
        {
            if (!CalibrationDataSupported())
            {
                _deadzone = Config.DefaultDeadzone;
                _deadzone2 = Config.DefaultDeadzone;
            }

            _activeStick1Deadzone = Config.DefaultDeadzone;
            _activeStick2Deadzone = Config.DefaultDeadzone;
        }

        if (oldConfig.DefaultRange != Config.DefaultRange)
        {
            if (!CalibrationDataSupported())
            {
                _range = Config.DefaultRange;
                _range2 = Config.DefaultRange;
            }

            _activeStick1Range = Config.DefaultRange;
            _activeStick2Range = Config.DefaultRange;
        }

        if (oldConfig.AllowCalibration != Config.AllowCalibration)
        {
            SetCalibration(Config.AllowCalibration);
        }
    }
    private class RumbleQueue
    {
        private const int MaxRumble = 15;
        private ConcurrentSpinQueue<float[]> _queue;

        public RumbleQueue(float[] rumbleInfo)
        {
            _queue = new(MaxRumble);
            _queue.Enqueue(rumbleInfo);
        }

        public void Enqueue(float lowFreq, float highFreq, float amplitude)
        {
            float[] rumble = { lowFreq, highFreq, amplitude };
            _queue.Enqueue(rumble);
        }

        private byte EncodeAmp(float amp)
        {
            byte enAmp;

            if (amp == 0)
            {
                enAmp = 0;
            }
            else if (amp < 0.117)
            {
                enAmp = (byte)((MathF.Log(amp * 1000, 2) * 32 - 0x60) / (5 - MathF.Pow(amp, 2)) - 1);
            }
            else if (amp < 0.23)
            {
                enAmp = (byte)(MathF.Log(amp * 1000, 2) * 32 - 0x60 - 0x5c);
            }
            else
            {
                enAmp = (byte)((MathF.Log(amp * 1000, 2) * 32 - 0x60) * 2 - 0xf6);
            }

            return enAmp;
        }

        public bool TryDequeue(out Span<byte> rumbleData)
        {
            if (!_queue.TryDequeue(out float[] queuedData))
            {
                rumbleData = null;
                return false;
            }

            rumbleData = new byte[8];

            if (queuedData[2] == 0.0f)
            {
                rumbleData[0] = 0x0;
                rumbleData[1] = 0x1;
                rumbleData[2] = 0x40;
                rumbleData[3] = 0x40;
            }
            else
            {
                queuedData[0] = Math.Clamp(queuedData[0], 40.875885f, 626.286133f);
                queuedData[1] = Math.Clamp(queuedData[1], 81.75177f, 1252.572266f);
                queuedData[2] = Math.Clamp(queuedData[2], 0.0f, 1.0f);

                var hf = (ushort)((MathF.Round(32f * MathF.Log(queuedData[1] * 0.1f, 2)) - 0x60) * 4);
                var lf = (byte)(MathF.Round(32f * MathF.Log(queuedData[0] * 0.1f, 2)) - 0x40);

                var hfAmp = EncodeAmp(queuedData[2]);
                var lfAmp = (ushort)(MathF.Round(hfAmp) * 0.5f); // weird rounding, is that correct ?

                var parity = (byte)(lfAmp % 2);
                if (parity > 0)
                {
                    --lfAmp;
                }

                lfAmp = (ushort)(lfAmp >> 1);
                lfAmp += 0x40;
                if (parity > 0)
                {
                    lfAmp |= 0x8000;
                }

                hfAmp = (byte)(hfAmp - hfAmp % 2); // make even at all times to prevent weird hum
                rumbleData[0] = (byte)(hf & 0xff);
                rumbleData[1] = (byte)(((hf >> 8) & 0xff) + hfAmp);
                rumbleData[2] = (byte)(((lfAmp >> 8) & 0xff) + lf);
                rumbleData[3] = (byte)(lfAmp & 0xff);
            }

            for (var i = 0; i < 4; ++i)
            {
                rumbleData[4 + i] = rumbleData[i];
            }

            return true;
        }

        public void Clear()
        {
            _queue.Clear();
        }
    }

    public struct IMUData
    {
        public short Xg;
        public short Yg;
        public short Zg;
        public short Xa;
        public short Ya;
        public short Za;

        public IMUData(short xg, short yg, short zg, short xa, short ya, short za)
        {
            Xg = xg;
            Yg = yg;
            Zg = zg;
            Xa = xa;
            Ya = ya;
            Za = za;
        }
    }

    public struct SticksData
    {
        public ushort Xs1;
        public ushort Ys1;
        public ushort Xs2;
        public ushort Ys2;

        public SticksData(ushort x1, ushort y1, ushort x2, ushort y2)
        {
            Xs1 = x1;
            Ys1 = y1;
            Xs2 = x2;
            Ys2 = y2;
        }
    }

    private class RollingAverage
    {
        private Queue<int> _samples;
        private int _size;
        private long _sum;

        public RollingAverage(int size)
        {
            _size = size;
            _samples = new Queue<int>(size);
            _sum = 0;
        }

        public void AddValue(int value)
        {
            if (_samples.Count >= _size)
            {
                int sample = _samples.Dequeue();
                _sum -= sample;
            }

            _samples.Enqueue(value);
            _sum += value;
        }

        public void Clear()
        {
            _samples.Clear();
            _sum = 0;
        }

        public bool Empty()
        {
            return _samples.Count == 0;
        }

        public float GetAverage()
        {
            return Empty() ? 0 : _sum / _samples.Count;
        }
    }
}
