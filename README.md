# LoRaWAN-SIM-2.4
A LoRaWAN simulator for 2.4GHz LoRa transceivers (Work in progress!)


## Features:
- Multiple half-duplex gateways (1 SF, 1 Channel)
- Two receive windows (RX1, RX2) for ACKs and commands
- Non-orthogonal SF transmissions
- Capture effect
- Path-loss signal attenuation model
- Multiple channels
- Collision handling for both uplink+downlink transmissions
- Proper header overhead
- Node energy consumption calculation (uplink+downlink)
- Downlink policies
- Adjustable packet size and rate

## Dependencies:
- https://metacpan.org/pod/Math::Random
- https://metacpan.org/pod/Term::ProgressBar
- https://metacpan.org/pod/GD::SVG

## Usage example:
```
perl generate_terrain.pl 800 100 1 > terrain.txt
perl LoRaWAN.pl 12 10000 terrain.txt
```
