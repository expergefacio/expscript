#include <OneWire.h>
#include <DallasTemperature.h>
#include <avr/sleep.h>
#include <avr/wdt.h>
#include <avr/interrupt.h>

#define TEMP_PIN   2
#define BUZZER_PIN 1

const float ARM_TEMP   = 57.0;
const float ALARM_TEMP = 55.0;

OneWire oneWire(TEMP_PIN);
DallasTemperature sensors(&oneWire);

bool armed = false;


// Disable watchdog before setup() runs.
void disableWatchdog()
    __attribute__((naked))
    __attribute__((section(".init3")));

void disableWatchdog() {
    MCUSR = 0;
    wdt_disable();
}  // <-- this closing brace is the important bit


// Watchdog interrupt: only wakes the ATtiny.
ISR(WDT_vect) {
}


// Sleep using the watchdog timer.
void sleepWDT(byte period) {
    cli();

    wdt_reset();
    MCUSR &= ~(1 << WDRF);

    WDTCR = (1 << WDCE) | (1 << WDE);
    WDTCR = (1 << WDIE) | period;

    set_sleep_mode(SLEEP_MODE_PWR_DOWN);
    sleep_enable();

    sei();
    sleep_cpu();

    sleep_disable();
    wdt_disable();
}


// About 20 seconds: 8 + 8 + 4.
void sleep20Seconds() {
    sleepWDT((1 << WDP3) | (1 << WDP0));  // 8 sec
    sleepWDT((1 << WDP3) | (1 << WDP0));  // 8 sec
    sleepWDT(1 << WDP3);                  // 4 sec
}


// About 32 seconds: 8 + 8 + 8 + 8.
void sleep32Seconds() {
    sleepWDT((1 << WDP3) | (1 << WDP0));
    sleepWDT((1 << WDP3) | (1 << WDP0));
    sleepWDT((1 << WDP3) | (1 << WDP0));
    sleepWDT((1 << WDP3) | (1 << WDP0));
}


// A-major alarm.
void playAlarm() {
    tone(BUZZER_PIN, 440);   // A4
    delay(300);

    tone(BUZZER_PIN, 554);   // C#5
    delay(300);

    tone(BUZZER_PIN, 659);   // E5
    delay(300);

    tone(BUZZER_PIN, 880);   // A5
    delay(500);

    noTone(BUZZER_PIN);
}


// Sleep permanently until reset or power cycle.
void sleepForever() {
    noTone(BUZZER_PIN);
    digitalWrite(BUZZER_PIN, LOW);

    set_sleep_mode(SLEEP_MODE_PWR_DOWN);
    sleep_enable();

    cli();
    sleep_cpu();

    while (true) {
    }
}


void setup() {    
    pinMode(BUZZER_PIN, OUTPUT);


    // Startup pip: D4 for 50 ms.
    tone(BUZZER_PIN, 294);
    delay(50);
    noTone(BUZZER_PIN);
    delay(500);

    sensors.begin();
    sensors.setResolution(10);

}


void loop() {
    sensors.requestTemperatures();
    float temp = sensors.getTempCByIndex(0);

    if (temp == DEVICE_DISCONNECTED_C) {
        sleep20Seconds();
        return;
    }


    // Arm once the drink reaches 62 °C.
    if (!armed && temp >= ARM_TEMP) {
        armed = true;

        // Confirmation chirp: A4 -> D4.
        tone(BUZZER_PIN, 440);
        delay(25);
        noTone(BUZZER_PIN);

        delay(500);

        tone(BUZZER_PIN, 294);
        delay(25);
        noTone(BUZZER_PIN);
    }


    // Once armed, alarm when temperature falls below 60 °C.
    if (armed && temp < ALARM_TEMP) {

        for (byte i = 0; i < 10; i++) {
            playAlarm();

            // ~32 seconds between alarms,
            // but no delay after the final alarm.
            if (i < 9) {
                sleep32Seconds();
            }
        }

        // Finished: sleep until reset/power-cycle.
        sleepForever();
    }


    // Sleep between temperature measurements.
    sleep20Seconds();
}

