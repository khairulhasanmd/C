run: test.c
	if [ -e test ]; then rm test; fi;
	gcc -Wall test.c -lcurl -lexpat -L/usr/local/ssl/lib -lssl -lcrypto -lm -o test.run
	./test.run