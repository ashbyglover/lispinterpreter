MLCC=mlton

all: lab4

lab1: ack.sml fib.sml splitter.sml
	$(MLCC) -output ack ack.sml
	$(MLCC) -output fib fib.sml
	$(MLCC) -output splitter splitter.sml

lab2: lab2.sml
	$(MLCC) -output lab2 lab2.sml

lab3: lab3.sml
	$(MLCC) -output lab3 lab3.sml

lab4: lab4.sml
	$(MLCC) -output lab4 lab4.sml
