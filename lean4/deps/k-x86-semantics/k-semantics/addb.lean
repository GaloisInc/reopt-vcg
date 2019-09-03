def addb1 : instruction :=
  definst "addb" $ do
    pattern fun (v_2511 : imm int) al => do
      v_4395 <- eval (handleImmediateWithSignExtend v_2511 8 8);
      v_4397 <- getRegister rax;
      v_4400 <- eval (add (concat (expression.bv_nat 1 0) v_4395) (concat (expression.bv_nat 1 0) (extract v_4397 56 64)));
      v_4402 <- eval (extract v_4400 1 2);
      v_4408 <- eval (extract v_4400 1 9);
      v_4412 <- eval (eq (extract v_4395 0 1) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_4397 0 56) v_4408);
      setRegister of (mux (bit_and (eq v_4412 (eq (extract v_4397 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_4412 (eq v_4402 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4408);
      setRegister zf (zeroFlag v_4408);
      setRegister af (bv_xor (bv_xor (extract v_4395 3 4) (extract v_4397 59 60)) (extract v_4400 4 5));
      setRegister sf v_4402;
      setRegister cf (extract v_4400 0 1);
      pure ()
    pat_end;
    pattern fun (v_2527 : imm int) (v_2530 : reg (bv 8)) => do
      v_4442 <- eval (handleImmediateWithSignExtend v_2527 8 8);
      v_4444 <- getRegister v_2530;
      v_4446 <- eval (add (concat (expression.bv_nat 1 0) v_4442) (concat (expression.bv_nat 1 0) v_4444));
      v_4448 <- eval (extract v_4446 1 2);
      v_4449 <- eval (extract v_4446 1 9);
      v_4457 <- eval (eq (extract v_4442 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2530) v_4449;
      setRegister of (mux (bit_and (eq v_4457 (eq (extract v_4444 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4457 (eq v_4448 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4449);
      setRegister af (bv_xor (extract (bv_xor v_4442 v_4444) 3 4) (extract v_4446 4 5));
      setRegister zf (zeroFlag v_4449);
      setRegister sf v_4448;
      setRegister cf (extract v_4446 0 1);
      pure ()
    pat_end;
    pattern fun (v_2538 : reg (bv 8)) (v_2539 : reg (bv 8)) => do
      v_4477 <- getRegister v_2538;
      v_4479 <- getRegister v_2539;
      v_4481 <- eval (add (concat (expression.bv_nat 1 0) v_4477) (concat (expression.bv_nat 1 0) v_4479));
      v_4483 <- eval (extract v_4481 1 2);
      v_4484 <- eval (extract v_4481 1 9);
      v_4492 <- eval (eq (extract v_4477 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2539) v_4484;
      setRegister of (mux (bit_and (eq v_4492 (eq (extract v_4479 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4492 (eq v_4483 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4484);
      setRegister af (bv_xor (extract (bv_xor v_4477 v_4479) 3 4) (extract v_4481 4 5));
      setRegister zf (zeroFlag v_4484);
      setRegister sf v_4483;
      setRegister cf (extract v_4481 0 1);
      pure ()
    pat_end;
    pattern fun (v_2546 : imm int) (v_2549 : reg (bv 8)) => do
      v_4539 <- eval (handleImmediateWithSignExtend v_2546 8 8);
      v_4541 <- getRegister v_2549;
      v_4543 <- eval (add (concat (expression.bv_nat 1 0) v_4539) (concat (expression.bv_nat 1 0) v_4541));
      v_4545 <- eval (extract v_4543 1 2);
      v_4550 <- eval (extract v_4543 1 9);
      v_4554 <- eval (eq (extract v_4539 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2549) v_4550;
      setRegister of (mux (bit_and (eq v_4554 (eq (extract v_4541 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4554 (eq v_4545 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4550);
      setRegister zf (zeroFlag v_4550);
      setRegister af (bv_xor (extract (bv_xor v_4539 v_4541) 3 4) (extract v_4543 4 5));
      setRegister sf v_4545;
      setRegister cf (extract v_4543 0 1);
      pure ()
    pat_end;
    pattern fun (v_2558 : reg (bv 8)) (v_2557 : reg (bv 8)) => do
      v_4574 <- getRegister v_2558;
      v_4576 <- getRegister v_2557;
      v_4578 <- eval (add (concat (expression.bv_nat 1 0) v_4574) (concat (expression.bv_nat 1 0) v_4576));
      v_4580 <- eval (extract v_4578 1 2);
      v_4585 <- eval (extract v_4578 1 9);
      v_4589 <- eval (eq (extract v_4574 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2557) v_4585;
      setRegister of (mux (bit_and (eq v_4589 (eq (extract v_4576 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4589 (eq v_4580 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4585);
      setRegister zf (zeroFlag v_4585);
      setRegister af (bv_xor (extract (bv_xor v_4574 v_4576) 3 4) (extract v_4578 4 5));
      setRegister sf v_4580;
      setRegister cf (extract v_4578 0 1);
      pure ()
    pat_end;
    pattern fun (v_2533 : Mem) (v_2534 : reg (bv 8)) => do
      v_9002 <- evaluateAddress v_2533;
      v_9003 <- load v_9002 1;
      v_9005 <- getRegister v_2534;
      v_9007 <- eval (add (concat (expression.bv_nat 1 0) v_9003) (concat (expression.bv_nat 1 0) v_9005));
      v_9009 <- eval (extract v_9007 1 2);
      v_9014 <- eval (extract v_9007 1 9);
      v_9018 <- eval (eq (extract v_9003 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2534) v_9014;
      setRegister of (mux (bit_and (eq v_9018 (eq (extract v_9005 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9018 (eq v_9009 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_9014);
      setRegister zf (zeroFlag v_9014);
      setRegister af (bv_xor (extract (bv_xor v_9003 v_9005) 3 4) (extract v_9007 4 5));
      setRegister sf v_9009;
      setRegister cf (extract v_9007 0 1);
      pure ()
    pat_end;
    pattern fun (v_2515 : imm int) (v_2517 : Mem) => do
      v_10572 <- evaluateAddress v_2517;
      v_10573 <- eval (handleImmediateWithSignExtend v_2515 8 8);
      v_10575 <- load v_10572 1;
      v_10577 <- eval (add (concat (expression.bv_nat 1 0) v_10573) (concat (expression.bv_nat 1 0) v_10575));
      v_10578 <- eval (extract v_10577 1 9);
      store v_10572 v_10578 1;
      v_10581 <- eval (extract v_10577 1 2);
      v_10589 <- eval (eq (extract v_10573 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10589 (eq (extract v_10575 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10589 (eq v_10581 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10578);
      setRegister af (bv_xor (extract (bv_xor v_10573 v_10575) 3 4) (extract v_10577 4 5));
      setRegister zf (zeroFlag v_10578);
      setRegister sf v_10581;
      setRegister cf (extract v_10577 0 1);
      pure ()
    pat_end;
    pattern fun (v_2521 : reg (bv 8)) (v_2520 : Mem) => do
      v_10604 <- evaluateAddress v_2520;
      v_10605 <- getRegister v_2521;
      v_10607 <- load v_10604 1;
      v_10609 <- eval (add (concat (expression.bv_nat 1 0) v_10605) (concat (expression.bv_nat 1 0) v_10607));
      v_10610 <- eval (extract v_10609 1 9);
      store v_10604 v_10610 1;
      v_10613 <- eval (extract v_10609 1 2);
      v_10621 <- eval (eq (extract v_10605 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10621 (eq (extract v_10607 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10621 (eq v_10613 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10610);
      setRegister af (bv_xor (extract (bv_xor v_10605 v_10607) 3 4) (extract v_10609 4 5));
      setRegister zf (zeroFlag v_10610);
      setRegister sf v_10613;
      setRegister cf (extract v_10609 0 1);
      pure ()
    pat_end
