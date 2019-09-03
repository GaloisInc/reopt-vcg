def vhsubps1 : instruction :=
  definst "vhsubps" $ do
    pattern fun (v_2442 : reg (bv 128)) (v_2443 : reg (bv 128)) (v_2444 : reg (bv 128)) => do
      v_4314 <- getRegister v_2442;
      v_4315 <- eval (extract v_4314 32 64);
      v_4323 <- eval (extract v_4314 0 32);
      v_4333 <- eval (extract v_4314 96 128);
      v_4341 <- eval (extract v_4314 64 96);
      v_4352 <- getRegister v_2443;
      v_4353 <- eval (extract v_4352 32 64);
      v_4361 <- eval (extract v_4352 0 32);
      v_4372 <- eval (extract v_4352 96 128);
      v_4380 <- eval (extract v_4352 64 96);
      setRegister (lhs.of_reg v_2444) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4315 0 1)) (uvalueMInt (extract v_4315 1 9)) (uvalueMInt (extract v_4315 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4323 0 1)) (uvalueMInt (extract v_4323 1 9)) (uvalueMInt (extract v_4323 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4333 0 1)) (uvalueMInt (extract v_4333 1 9)) (uvalueMInt (extract v_4333 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4341 0 1)) (uvalueMInt (extract v_4341 1 9)) (uvalueMInt (extract v_4341 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4353 0 1)) (uvalueMInt (extract v_4353 1 9)) (uvalueMInt (extract v_4353 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4361 0 1)) (uvalueMInt (extract v_4361 1 9)) (uvalueMInt (extract v_4361 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4372 0 1)) (uvalueMInt (extract v_4372 1 9)) (uvalueMInt (extract v_4372 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4380 0 1)) (uvalueMInt (extract v_4380 1 9)) (uvalueMInt (extract v_4380 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2453 : reg (bv 256)) (v_2454 : reg (bv 256)) (v_2455 : reg (bv 256)) => do
      v_4397 <- getRegister v_2453;
      v_4398 <- eval (extract v_4397 32 64);
      v_4406 <- eval (extract v_4397 0 32);
      v_4416 <- eval (extract v_4397 96 128);
      v_4424 <- eval (extract v_4397 64 96);
      v_4435 <- getRegister v_2454;
      v_4436 <- eval (extract v_4435 32 64);
      v_4444 <- eval (extract v_4435 0 32);
      v_4455 <- eval (extract v_4435 96 128);
      v_4463 <- eval (extract v_4435 64 96);
      v_4474 <- eval (extract v_4397 160 192);
      v_4482 <- eval (extract v_4397 128 160);
      v_4492 <- eval (extract v_4397 224 256);
      v_4500 <- eval (extract v_4397 192 224);
      v_4511 <- eval (extract v_4435 160 192);
      v_4519 <- eval (extract v_4435 128 160);
      v_4530 <- eval (extract v_4435 224 256);
      v_4538 <- eval (extract v_4435 192 224);
      setRegister (lhs.of_reg v_2455) (concat (concat (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4398 0 1)) (uvalueMInt (extract v_4398 1 9)) (uvalueMInt (extract v_4398 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4406 0 1)) (uvalueMInt (extract v_4406 1 9)) (uvalueMInt (extract v_4406 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4416 0 1)) (uvalueMInt (extract v_4416 1 9)) (uvalueMInt (extract v_4416 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4424 0 1)) (uvalueMInt (extract v_4424 1 9)) (uvalueMInt (extract v_4424 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4436 0 1)) (uvalueMInt (extract v_4436 1 9)) (uvalueMInt (extract v_4436 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4444 0 1)) (uvalueMInt (extract v_4444 1 9)) (uvalueMInt (extract v_4444 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4455 0 1)) (uvalueMInt (extract v_4455 1 9)) (uvalueMInt (extract v_4455 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4463 0 1)) (uvalueMInt (extract v_4463 1 9)) (uvalueMInt (extract v_4463 9 32)))) 32)) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4474 0 1)) (uvalueMInt (extract v_4474 1 9)) (uvalueMInt (extract v_4474 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4482 0 1)) (uvalueMInt (extract v_4482 1 9)) (uvalueMInt (extract v_4482 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4492 0 1)) (uvalueMInt (extract v_4492 1 9)) (uvalueMInt (extract v_4492 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4500 0 1)) (uvalueMInt (extract v_4500 1 9)) (uvalueMInt (extract v_4500 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4511 0 1)) (uvalueMInt (extract v_4511 1 9)) (uvalueMInt (extract v_4511 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4519 0 1)) (uvalueMInt (extract v_4519 1 9)) (uvalueMInt (extract v_4519 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4530 0 1)) (uvalueMInt (extract v_4530 1 9)) (uvalueMInt (extract v_4530 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4538 0 1)) (uvalueMInt (extract v_4538 1 9)) (uvalueMInt (extract v_4538 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2437 : Mem) (v_2438 : reg (bv 128)) (v_2439 : reg (bv 128)) => do
      v_10376 <- evaluateAddress v_2437;
      v_10377 <- load v_10376 16;
      v_10378 <- eval (extract v_10377 32 64);
      v_10386 <- eval (extract v_10377 0 32);
      v_10396 <- eval (extract v_10377 96 128);
      v_10404 <- eval (extract v_10377 64 96);
      v_10415 <- getRegister v_2438;
      v_10416 <- eval (extract v_10415 32 64);
      v_10424 <- eval (extract v_10415 0 32);
      v_10435 <- eval (extract v_10415 96 128);
      v_10443 <- eval (extract v_10415 64 96);
      setRegister (lhs.of_reg v_2439) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10378 0 1)) (uvalueMInt (extract v_10378 1 9)) (uvalueMInt (extract v_10378 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10386 0 1)) (uvalueMInt (extract v_10386 1 9)) (uvalueMInt (extract v_10386 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10396 0 1)) (uvalueMInt (extract v_10396 1 9)) (uvalueMInt (extract v_10396 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10404 0 1)) (uvalueMInt (extract v_10404 1 9)) (uvalueMInt (extract v_10404 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10416 0 1)) (uvalueMInt (extract v_10416 1 9)) (uvalueMInt (extract v_10416 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10424 0 1)) (uvalueMInt (extract v_10424 1 9)) (uvalueMInt (extract v_10424 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10435 0 1)) (uvalueMInt (extract v_10435 1 9)) (uvalueMInt (extract v_10435 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10443 0 1)) (uvalueMInt (extract v_10443 1 9)) (uvalueMInt (extract v_10443 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2448 : Mem) (v_2449 : reg (bv 256)) (v_2450 : reg (bv 256)) => do
      v_10455 <- evaluateAddress v_2448;
      v_10456 <- load v_10455 32;
      v_10457 <- eval (extract v_10456 32 64);
      v_10465 <- eval (extract v_10456 0 32);
      v_10475 <- eval (extract v_10456 96 128);
      v_10483 <- eval (extract v_10456 64 96);
      v_10494 <- getRegister v_2449;
      v_10495 <- eval (extract v_10494 32 64);
      v_10503 <- eval (extract v_10494 0 32);
      v_10514 <- eval (extract v_10494 96 128);
      v_10522 <- eval (extract v_10494 64 96);
      v_10533 <- eval (extract v_10456 160 192);
      v_10541 <- eval (extract v_10456 128 160);
      v_10551 <- eval (extract v_10456 224 256);
      v_10559 <- eval (extract v_10456 192 224);
      v_10570 <- eval (extract v_10494 160 192);
      v_10578 <- eval (extract v_10494 128 160);
      v_10589 <- eval (extract v_10494 224 256);
      v_10597 <- eval (extract v_10494 192 224);
      setRegister (lhs.of_reg v_2450) (concat (concat (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10457 0 1)) (uvalueMInt (extract v_10457 1 9)) (uvalueMInt (extract v_10457 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10465 0 1)) (uvalueMInt (extract v_10465 1 9)) (uvalueMInt (extract v_10465 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10475 0 1)) (uvalueMInt (extract v_10475 1 9)) (uvalueMInt (extract v_10475 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10483 0 1)) (uvalueMInt (extract v_10483 1 9)) (uvalueMInt (extract v_10483 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10495 0 1)) (uvalueMInt (extract v_10495 1 9)) (uvalueMInt (extract v_10495 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10503 0 1)) (uvalueMInt (extract v_10503 1 9)) (uvalueMInt (extract v_10503 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10514 0 1)) (uvalueMInt (extract v_10514 1 9)) (uvalueMInt (extract v_10514 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10522 0 1)) (uvalueMInt (extract v_10522 1 9)) (uvalueMInt (extract v_10522 9 32)))) 32)) (concat (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10533 0 1)) (uvalueMInt (extract v_10533 1 9)) (uvalueMInt (extract v_10533 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10541 0 1)) (uvalueMInt (extract v_10541 1 9)) (uvalueMInt (extract v_10541 9 32)))) 32) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10551 0 1)) (uvalueMInt (extract v_10551 1 9)) (uvalueMInt (extract v_10551 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10559 0 1)) (uvalueMInt (extract v_10559 1 9)) (uvalueMInt (extract v_10559 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10570 0 1)) (uvalueMInt (extract v_10570 1 9)) (uvalueMInt (extract v_10570 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10578 0 1)) (uvalueMInt (extract v_10578 1 9)) (uvalueMInt (extract v_10578 9 32)))) 32)) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10589 0 1)) (uvalueMInt (extract v_10589 1 9)) (uvalueMInt (extract v_10589 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10597 0 1)) (uvalueMInt (extract v_10597 1 9)) (uvalueMInt (extract v_10597 9 32)))) 32)));
      pure ()
    pat_end
