all: clean run

run: clean 
	@echo "Run compilation, elaborate and simulation"
	bash ./run.sh

clean:
	@echo "Cleaning build artifacts..."
	rm -rf ./build
