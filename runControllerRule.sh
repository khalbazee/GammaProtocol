certoraRun specs/ControllerHarness.sol contracts/MarginPool.sol:MarginPool specs/OtokenHarnessA.sol specs/OtokenHarnessB.sol specs/DummyERC20A.sol specs/DummyERC20B.sol specs/DummyERC20C.sol --link ControllerHarness:pool=MarginPool ControllerHarness:anOtokenA=OtokenHarnessA ControllerHarness:anOtokenB=OtokenHarnessB ControllerHarness:dummyERC20C=DummyERC20C OtokenHarnessA:underlyingAsset=DummyERC20A OtokenHarnessA:strikeAsset=DummyERC20B OtokenHarnessA:collateralAsset=DummyERC20C OtokenHarnessB:underlyingAsset=DummyERC20A OtokenHarnessB:strikeAsset=DummyERC20B OtokenHarnessB:collateralAsset=DummyERC20C --solc solc6.10 --verify ControllerHarness:specs/Controller.spec  --settings  -assumeUnwindCond,-b=3,-enableStorageVariableUnpacking=false,-deleteSMTFile=true,-graphDrawLimit=0,-skipCounterExamples=false,-t=60,-lowFootprint=true --staging shelly/newInlining2 --settings -rule=$1
