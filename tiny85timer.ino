#include <HT1621.h>
#include <EEPROM.h>
#include <avr/sleep.h>
#include <avr/interrupt.h>

//use Digistump avr boards
//clock set to 1mhz - no usb



#define LCD_CS    3     // PB3
#define LCD_WR    4     // PB4
#define LCD_DATA  0     // PB0

#define BUZZER_PIN PB1

HT1621 lcd;

enum ButtonState {
  NONE,
  BTN1,
  BTN2,
  BTN3,
  SHIFT,
  SHIFT_BTN1,
  SHIFT_BTN2,
  SHIFT_BTN3
};


// ============================================================
// SLEEP
// ============================================================

const uint32_t SLEEP_AFTER_MS = 30000UL;   // 30 sec idle
uint32_t lastActivityAt = 0;


// Empty ISR: its only job is to wake the CPU
ISR(PCINT0_vect) {
}


void enterDeepSleep() {

  // ADC off while sleeping
  ADCSRA &= ~_BV(ADEN);

  // PB2 / PCINT2 is our wake input
  PCMSK |= _BV(PCINT2);

  // Clear any old pending pin-change flag
  GIFR |= _BV(PCIF);

  // Enable pin-change interrupts
  GIMSK |= _BV(PCIE);

  set_sleep_mode(SLEEP_MODE_PWR_DOWN);

  cli();
  sleep_enable();

  // Important:
  // if a button became pressed just before sleeping,
  // don't go to sleep and miss it.
  if (PINB & _BV(PB2)) {
    sleep_disable();
    sei();

    GIMSK &= ~_BV(PCIE);
    ADCSRA |= _BV(ADEN);

    return;
  }

  sei();
  sleep_cpu();

  // -------- wakes here --------

  sleep_disable();

  GIMSK &= ~_BV(PCIE);

  // ADC back on for button identification
  ADCSRA |= _BV(ADEN);
}

// ============================================================
// TIMER STORED PRESET
// ============================================================

uint32_t presetMs = 0;
uint32_t remainingMs = 0;


// ============================================================
// EEPROM
// ============================================================

#define EEPROM_MAGIC_ADDR   0
#define EEPROM_TIME_ADDR    1
#define EEPROM_MAGIC        0xA7

void savePreset() {
  EEPROM.update(EEPROM_MAGIC_ADDR, EEPROM_MAGIC);

  EEPROM.update(EEPROM_TIME_ADDR + 0, (presetMs >>  0) & 0xFF);
  EEPROM.update(EEPROM_TIME_ADDR + 1, (presetMs >>  8) & 0xFF);
  EEPROM.update(EEPROM_TIME_ADDR + 2, (presetMs >> 16) & 0xFF);
  EEPROM.update(EEPROM_TIME_ADDR + 3, (presetMs >> 24) & 0xFF);
}

void loadPreset() {

  if (EEPROM.read(EEPROM_MAGIC_ADDR) != EEPROM_MAGIC) {
    presetMs = 0;
    remainingMs = 0;
    return;
  }

  presetMs =
      ((uint32_t)EEPROM.read(EEPROM_TIME_ADDR + 0) <<  0) |
      ((uint32_t)EEPROM.read(EEPROM_TIME_ADDR + 1) <<  8) |
      ((uint32_t)EEPROM.read(EEPROM_TIME_ADDR + 2) << 16) |
      ((uint32_t)EEPROM.read(EEPROM_TIME_ADDR + 3) << 24);

  if (presetMs > 5999UL * 1000UL)
    presetMs = 0;

  remainingMs = presetMs;
}

bool resetArmed = false;
uint32_t resetArmedAt = 0;

const uint32_t DOUBLE_RESET_MS = 2000UL;

bool presetDirty = false;

// ============================================================
// BATTERY VOLTAGE
// ============================================================

// Calibrated from this ATtiny85:
// USB supply treated as exactly 5.00 V
const uint32_t VCC_CALIBRATION = 1135484UL;

uint8_t batteryLevel = 3;


uint16_t readVccMillivolts() {

  // VCC is ADC reference.
  // Measure internal ~1.1 V bandgap.
  ADMUX = _BV(MUX3) | _BV(MUX2);

  ADCSRA =
      _BV(ADEN) |
      _BV(ADPS1) |
      _BV(ADPS0);

  delay(3);

  // Throw away first reading
  ADCSRA |= _BV(ADSC);
  while (ADCSRA & _BV(ADSC));

  uint32_t total = 0;

  // Average 8 samples
  for (uint8_t i = 0; i < 8; i++) {
    ADCSRA |= _BV(ADSC);
    while (ADCSRA & _BV(ADSC));

    total += ADC;
  }

  uint16_t adc = total / 8;

  if (adc == 0)
    return 0;

  return VCC_CALIBRATION / adc;
}


uint8_t batteryLevelFromVoltage(uint16_t mv) {

  // 3 × LR44 usable range approximately 4.6 -> 3.5 V
  //
  // 3 bars = healthy
  // 2 bars = getting down
  // 1 bar  = low
  //
  // We deliberately always show at least one bar.

  if (mv >= 4200)
    return 3;

  if (mv >= 3800)
    return 2;

  return 1;
}


void updateBatteryLevel() {
  batteryLevel = batteryLevelFromVoltage(readVccMillivolts());
}


// ============================================================
// BUTTONS
// PB2 = ADC1
// ============================================================


int readButtons() {
  return analogRead(1);   // PB2 = ADC1
}


ButtonState decodeButton(int v) {
  if (v > 900) return SHIFT_BTN1;  // ~915
  if (v > 868) return BTN1;        // ~884
  if (v > 833) return SHIFT_BTN2;  // ~851
  if (v > 785) return SHIFT_BTN3;  // ~814
  if (v > 726) return BTN2;        // ~756
  if (v > 675) return SHIFT;       // ~695
  if (v > 550) return BTN3;        // ~654

  return NONE;
}


uint8_t heldButtonCount(ButtonState b) {
  switch (b) {
    case SHIFT_BTN1:
    case SHIFT_BTN2:
    case SHIFT_BTN3:
      return 2;

    case BTN1:
    case BTN2:
    case BTN3:
    case SHIFT:
      return 1;

    default:
      return 0;
  }
}


// ============================================================
// BUZZER
// ============================================================

void beep(uint16_t freq, uint16_t durationMs) {
  uint32_t halfPeriod = 500000UL / freq;
  uint32_t cycles =
      ((uint32_t)freq * durationMs) / 1000;

  for (uint32_t i = 0; i < cycles; i++) {
    PORTB |= _BV(BUZZER_PIN);
    delayMicroseconds(halfPeriod);

    PORTB &= ~_BV(BUZZER_PIN);
    delayMicroseconds(halfPeriod);
  }

  PORTB &= ~_BV(BUZZER_PIN);
}


void warningChirp(uint8_t highMs = 55, uint8_t lowMs = 25) {
  beep(2300, highMs);
  beep(750, lowMs);
}

// tiny acknowledgement blip
void buttonBlip() {
  beep(750, 3);
}


// 10-second warning
void tenSecondWarning() {
  // first strike
  warningChirp(55, 25);

  delay(200);

  // second slightly shorter strike
  warningChirp(45, 25);
}


// ============================================================
// LCD RAW DIGIT WRITING
//
// We still let the HT1621 library initialise the display.
// These routines only replace its digit-buffer formatting so
// that we can force MM.SS with leading zeroes.
// ============================================================

const uint8_t digitSegments[10] = {
  0x7D, // 0
  0x60, // 1
  0x3E, // 2
  0x7A, // 3
  0x63, // 4
  0x5B, // 5
  0x5F, // 6
  0x70, // 7
  0x7F, // 8
  0x7B  // 9
};


void lcdSendBits(uint8_t data, uint8_t count) {
  for (uint8_t i = 0; i < count; i++) {
    digitalWrite(LCD_WR, LOW);
    delayMicroseconds(4);

    digitalWrite(
      LCD_DATA,
      (data & 0x80) ? HIGH : LOW
    );

    digitalWrite(LCD_WR, HIGH);
    delayMicroseconds(4);

    data <<= 1;
  }
}


void lcdWriteByte(uint8_t addr, uint8_t data) {
  addr <<= 2;

  digitalWrite(LCD_CS, LOW);

  lcdSendBits(0xA0, 3);
  lcdSendBits(addr, 6);
  lcdSendBits(data, 8);

  digitalWrite(LCD_CS, HIGH);
}


// show MM.SS
void displayTime(uint32_t totalSeconds) {

  if (totalSeconds > 5999)
    totalSeconds = 5999;   // 99:59 max

  uint8_t minutes = totalSeconds / 60;
  uint8_t seconds = totalSeconds % 60;

  uint8_t buffer[6];

  // Two unused leftmost digits
  buffer[0] = 0;
  buffer[1] = 0;

  buffer[2] = digitSegments[minutes / 10];
  buffer[3] = digitSegments[minutes % 10];

  // Decimal point is carried in bit 7 of this position
  buffer[4] = digitSegments[seconds / 10] | 0x80;
  buffer[5] = digitSegments[seconds % 10];


  // Battery indicator
  //
  // HT1621 library mapping:
  // level 1 → buffer[2] bit 7
  // level 2 → + buffer[1] bit 7
  // level 3 → + buffer[0] bit 7

  if (batteryLevel >= 1)
    buffer[2] |= 0x80;

  if (batteryLevel >= 2)
    buffer[1] |= 0x80;

  if (batteryLevel >= 3)
    buffer[0] |= 0x80;

  // HT1621 glass is wired backwards relative to buffer
  lcdWriteByte(0,  buffer[5]);
  lcdWriteByte(2,  buffer[4]);
  lcdWriteByte(4,  buffer[3]);
  lcdWriteByte(6,  buffer[2]);
  lcdWriteByte(8,  buffer[1]);
  lcdWriteByte(10, buffer[0]);
}


// ============================================================
// TIMER
// ============================================================


bool running = false;

uint32_t runStartedAt = 0;
uint32_t runStartedWith = 0;

uint32_t previousRemainingMs = 0;

bool tenSecondWarned = true;

uint32_t lastDisplayedSecond = 0xFFFFFFFFUL;

static bool firstRepeat = true;




uint32_t currentRemainingMs() {

  if (!running)
    return remainingMs;

  uint32_t elapsed = millis() - runStartedAt;

  if (elapsed >= runStartedWith)
    return 0;

  return runStartedWith - elapsed;
}


void refreshDisplay() {

  uint32_t r = currentRemainingMs();

  // Ceiling rather than floor:
  // 9.8 seconds still displays 00.10
  uint32_t seconds =
      (r == 0) ? 0 : ((r + 999) / 1000);

  if (seconds != lastDisplayedSecond) {
    displayTime(seconds);
    lastDisplayedSecond = seconds;
  }
}


void setRemaining(uint32_t newMs) {

  const uint32_t MAX_TIME =
      5999UL * 1000UL; // 99:59

  if (newMs > MAX_TIME)
    newMs = MAX_TIME;

  remainingMs = newMs;

  if (running) {
    runStartedWith = remainingMs;
    runStartedAt = millis();
  }

  lastDisplayedSecond = 0xFFFFFFFFUL;
  refreshDisplay();
}


void adjustTime(int32_t deltaMs) {
  resetArmed = false;

  // Normally adjustments happen while stopped/paused.
  uint32_t base = running ? currentRemainingMs() : remainingMs;

  int32_t newValue = (int32_t)base + deltaMs;

  if (newValue < 0)
    newValue = 0;

  const uint32_t MAX_TIME = 5999UL * 1000UL;

  if ((uint32_t)newValue > MAX_TIME)
    newValue = MAX_TIME;

  presetMs = (uint32_t)newValue;
  remainingMs = presetMs;

  presetDirty = true;

  running = false;

  // Persist the newly selected time
  //savePreset();

  lastDisplayedSecond = 0xFFFFFFFFUL;
  refreshDisplay();
}


void startTimer() {

  resetArmed = false;

  if (running || remainingMs == 0)
    return;

  updateBatteryLevel();

  lastDisplayedSecond = 0xFFFFFFFFUL;
  refreshDisplay();

  running = true;

  runStartedWith = remainingMs;
  runStartedAt = millis();

  previousRemainingMs = remainingMs;

  if (remainingMs == 3000UL) {
    warningChirp(55, 25);
  }

  tenSecondWarned = (remainingMs <= 10000UL);
}


void pauseTimer() {
  resetArmed = false;

  if (!running)
    return;

  remainingMs = currentRemainingMs();
  running = false;

  lastDisplayedSecond = 0xFFFFFFFFUL;
  refreshDisplay();
}


void resetTimer() {
  running = false;

  // Second reset within 2 seconds = erase preset
  if (resetArmed &&
      millis() - resetArmedAt <= DOUBLE_RESET_MS) {

    presetMs = 0;
    remainingMs = 0;

    presetDirty = false;

    savePreset();

    resetArmed = false;
    tenSecondWarned = true;

    lastDisplayedSecond = 0xFFFFFFFFUL;
    refreshDisplay();

    return;
  }

  // First reset = restore original preset
  remainingMs = presetMs;

  resetArmed = true;
  resetArmedAt = millis();

  tenSecondWarned = true;

  lastDisplayedSecond = 0xFFFFFFFFUL;
  refreshDisplay();
}



// ============================================================
// MAIN ALARM
// ============================================================

bool anyButtonPressed() {
  return readButtons() > 550;
}


bool alarmStrike(uint16_t freq, uint8_t durationMs) {

  beep(freq, durationMs);

  return anyButtonPressed();
}


// ------------------------------------------------------------
// 500 ms "dual bell" burst
//
// 2300 Hz = loud / harsh on our buzzer
//  750 Hz = lower ANC-troublesome band
//
// Irregular timing prevents it sounding like a simple
// alternating two-note siren.
// ------------------------------------------------------------

bool duoBellBurst() {

  if (alarmStrike(2300, 55)) return true;
  if (alarmStrike( 750, 25)) return true;

  if (alarmStrike(2300, 45)) return true;
  if (alarmStrike( 750, 30)) return true;

  if (alarmStrike(2300, 60)) return true;
  if (alarmStrike( 750, 25)) return true;

  if (alarmStrike(2300, 40)) return true;
  if (alarmStrike( 750, 35)) return true;

  if (alarmStrike(2300, 55)) return true;
  if (alarmStrike( 750, 25)) return true;

  if (alarmStrike(2300, 60)) return true;
  if (alarmStrike( 750, 45)) return true;

  // total = 500 ms
  return false;
}


bool alarmSilence() {

  // leave this exactly as you currently have it
  for (uint8_t i = 0; i < 4; i++) {
    delay(50);

    if (anyButtonPressed())
      return true;
  }

  return false;
}


void waitForButtonsReleased() {
  while (anyButtonPressed())
    delay(10);

  delay(30);
}


void runAlarm() {

  // 86 × 700 ms ≈ 60.2 seconds maximum
  for (uint8_t alarmCycle = 0;
       alarmCycle < 86;
       alarmCycle++) {

    // 500 ms dual-frequency nasty bell
    if (duoBellBurst()) {
      waitForButtonsReleased();
      return;
    }

    // 200 ms OFF
    if (alarmSilence()) {
      waitForButtonsReleased();
      return;
    }
  }
}


// ============================================================
// BUTTON ACTIONS
// ============================================================

bool isAdjustmentButton(ButtonState b) {

  return
    b == BTN1 ||
    b == SHIFT_BTN1 ||
    b == BTN2 ||
    b == SHIFT_BTN2;
}


void initialButtonAction(ButtonState b) {

  switch (b) {

    // BTN1 = MINUTES
    case BTN1:
      adjustTime(+60000L);
      break;

    case SHIFT_BTN1:
      adjustTime(-60000L);
      break;


    // BTN2 = SECONDS
    case BTN2:
      adjustTime(+1000L);
      break;

    case SHIFT_BTN2:
      adjustTime(-1000L);
      break;


    case BTN3:

      if (running)
        pauseTimer();
      else
        startTimer();

      break;

    case SHIFT_BTN3:
      resetTimer();
      break;


    default:
      break;
  }
}


void repeatHeldAction(ButtonState b) {

  switch (b) {

    // BTN1 = +/- 5 minutes per second held
    case BTN1:
      adjustTime(+300000L);
      break;

    case SHIFT_BTN1:
      adjustTime(-300000L);
      break;


    // BTN2 = +/- 5 seconds per second held
    case BTN2:
      adjustTime(+5000L);
      break;

    case SHIFT_BTN2:
      adjustTime(-5000L);
      break;


    default:
      break;
  }
}


// ============================================================
// SETUP
// ============================================================

void setup() {

  lastActivityAt = millis();

  // Buzzer
  DDRB |= _BV(BUZZER_PIN);
  PORTB &= ~_BV(BUZZER_PIN);

  // Button ladder PB2 / ADC1
  DDRB &= ~_BV(PB2);
  PORTB &= ~_BV(PB2);

  // LCD
  lcd.begin(LCD_CS, LCD_WR, LCD_DATA);

  lcd.clear();

  updateBatteryLevel();

  loadPreset();

  displayTime((presetMs + 999) / 1000);

  delay(100);

  // one boot beep
  beep(750, 30);
}


// ============================================================
// LOOP
// ============================================================

void loop() {


  // ----------------------------------------------------------
  // TIMER UPDATE
  // ----------------------------------------------------------

  if (running) {

    uint32_t r = currentRemainingMs();

    // 10-second warning
    if (!tenSecondWarned &&
        previousRemainingMs > 10000UL &&
        r <= 10000UL) {

      tenSecondWarned = true;

      tenSecondWarning();
    }

    // Final 3... 2... 1 countdown chirps
    if (previousRemainingMs > 3000UL && r <= 3000UL) {
      warningChirp(55, 25);
    }

    if (previousRemainingMs > 2000UL && r <= 2000UL) {
      warningChirp(55, 25);
    }

    if (previousRemainingMs > 1000UL && r <= 1000UL) {
      warningChirp(55, 25);
    }

    previousRemainingMs = r;

    if (r == 0) {

      running = false;

      // Countdown itself reaches zero
      displayTime(0);
      lastDisplayedSecond = 0;

      // Alarm until cancelled / timeout
      runAlarm();

      // IMPORTANT:
      // restore the original preset afterwards
      remainingMs = presetMs;

      lastDisplayedSecond = 0xFFFFFFFFUL;
      refreshDisplay();

      lastActivityAt = millis();

      return;
    }
  }

refreshDisplay();

  // ----------------------------------------------------------
  // BUTTON DEBOUNCE / STATE CHANGES
  // ----------------------------------------------------------

  static ButtonState stableState = NONE;
  static ButtonState rawState = NONE;

  static uint32_t rawChangedAt = 0;
  static uint32_t nextRepeatAt = 0;


  ButtonState now =
      decodeButton(readButtons());


  // raw state changed
  if (now != rawState) {

    rawState = now;
    rawChangedAt = millis();

    lastActivityAt = millis();
  }


  // stable for at least 20ms
  if (rawState != stableState &&
      millis() - rawChangedAt >= 20) {

    ButtonState oldState =
        stableState;

    stableState =
        rawState;

    // Save preset once after an adjustment button is released
    if (presetDirty && !isAdjustmentButton(stableState)) {
      savePreset();
      presetDirty = false;
    }

    // A physical button has been ADDED
    if (heldButtonCount(stableState) >
        heldButtonCount(oldState)) {

      buttonBlip();

      initialButtonAction(stableState);

      if (isAdjustmentButton(stableState)) {
        nextRepeatAt = millis() + 1000UL;
        firstRepeat = true;
      }
    }
  }


  // ----------------------------------------------------------
  // HOLD REPEAT
  //
  // Initial press = +/-1
  // after 1 second held:
  // +/-5 every second
  // ----------------------------------------------------------

  if (isAdjustmentButton(stableState) &&
      millis() >= nextRepeatAt) {

    if (firstRepeat) {

      switch (stableState) {

        // BTN1 = minutes
        case BTN1:
          adjustTime(+240000L);   // +4 min
          break;

        case SHIFT_BTN1:
          adjustTime(-240000L);   // -4 min
          break;

        // BTN2 = seconds
        case BTN2:
          adjustTime(+4000L);     // +4 sec
          break;

        case SHIFT_BTN2:
          adjustTime(-4000L);     // -4 sec
          break;

        default:
          break;
      }

      firstRepeat = false;

    } else {

      repeatHeldAction(stableState);   // normal ±5 thereafter
    }

    nextRepeatAt += 1000UL;
  }

  if (!running &&
      stableState == NONE &&
      rawState == NONE &&
      millis() - lastActivityAt >= SLEEP_AFTER_MS) {

    enterDeepSleep();


    updateBatteryLevel();

    // force LCD redraw so new battery level appears
    lastDisplayedSecond = 0xFFFFFFFFUL;
    refreshDisplay();

    // millis() stops during POWER_DOWN,
    // so restart the inactivity period after waking.
    lastActivityAt = millis();
  }

  delay(5);
}
