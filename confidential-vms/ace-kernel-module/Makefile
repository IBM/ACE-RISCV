CONFIG_MODULE_SIG=n

startstop-objs := start.o stop.o
obj-m += ace.o

ifeq ($(CONFIG_STATUS_CHECK_GCC),y)
	CC=$(STATUS_CHECK_GCC)
	ccflags-y += -fanalyzer
endif

KDIR ?= /lib/modules/$(shell uname -r)/build
PWD := $(CURDIR)

default:
	$(MAKE) -C $(KDIR) CC="$(CC)" M="$(PWD)" modules
	rm -f .Module* .modules* .ace* *.symvers *.order ace.mod.* *.o *.mod

load:
	@insmod ace.ko

clean:
	$(MAKE) -C /lib/modules/$(shell uname -r)/build CC="$(CC)" M="$(PWD)" clean
	$(RM) other/cat_noblock *.plist

indent:
	clang-format -i *[.ch]
	clang-format -i other/*[.ch]