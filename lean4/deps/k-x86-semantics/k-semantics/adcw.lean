def adcw1 : instruction :=
  definst "adcw" $ do
    pattern fun (v_2486 : imm int) ax => do
      v_4271 <- getRegister cf;
      v_4273 <- eval (handleImmediateWithSignExtend v_2486 16 16);
      v_4274 <- eval (concat (expression.bv_nat 1 0) v_4273);
      v_4277 <- getRegister rax;
      v_4280 <- eval (add (mux (eq v_4271 (expression.bv_nat 1 1)) (add v_4274 (expression.bv_nat 17 1)) v_4274) (concat (expression.bv_nat 1 0) (extract v_4277 48 64)));
      v_4282 <- eval (extract v_4280 1 2);
      v_4288 <- eval (extract v_4280 1 17);
      v_4293 <- eval (eq (extract v_4273 0 1) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_4277 0 48) v_4288);
      setRegister of (mux (bit_and (eq v_4293 (eq (extract v_4277 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_4293 (eq v_4282 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4280 9 17));
      setRegister zf (zeroFlag v_4288);
      setRegister af (bv_xor (bv_xor (extract v_4273 11 12) (extract v_4277 59 60)) (extract v_4280 12 13));
      setRegister sf v_4282;
      setRegister cf (extract v_4280 0 1);
      pure ()
    pat_end;
    pattern fun (v_2498 : imm int) (v_2500 : reg (bv 16)) => do
      v_4319 <- getRegister cf;
      v_4321 <- eval (handleImmediateWithSignExtend v_2498 16 16);
      v_4322 <- eval (concat (expression.bv_nat 1 0) v_4321);
      v_4325 <- getRegister v_2500;
      v_4327 <- eval (add (mux (eq v_4319 (expression.bv_nat 1 1)) (add v_4322 (expression.bv_nat 17 1)) v_4322) (concat (expression.bv_nat 1 0) v_4325));
      v_4329 <- eval (extract v_4327 1 2);
      v_4330 <- eval (extract v_4327 1 17);
      v_4339 <- eval (eq (extract v_4321 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2500) v_4330;
      setRegister of (mux (bit_and (eq v_4339 (eq (extract v_4325 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4339 (eq v_4329 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4327 9 17));
      setRegister af (bv_xor (extract (bv_xor v_4321 v_4325) 11 12) (extract v_4327 12 13));
      setRegister zf (zeroFlag v_4330);
      setRegister sf v_4329;
      setRegister cf (extract v_4327 0 1);
      pure ()
    pat_end;
    pattern fun (v_2508 : reg (bv 16)) (v_2509 : reg (bv 16)) => do
      v_4359 <- getRegister cf;
      v_4361 <- getRegister v_2508;
      v_4362 <- eval (concat (expression.bv_nat 1 0) v_4361);
      v_4365 <- getRegister v_2509;
      v_4367 <- eval (add (mux (eq v_4359 (expression.bv_nat 1 1)) (add v_4362 (expression.bv_nat 17 1)) v_4362) (concat (expression.bv_nat 1 0) v_4365));
      v_4369 <- eval (extract v_4367 1 2);
      v_4370 <- eval (extract v_4367 1 17);
      v_4379 <- eval (eq (extract v_4361 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2509) v_4370;
      setRegister of (mux (bit_and (eq v_4379 (eq (extract v_4365 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4379 (eq v_4369 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4367 9 17));
      setRegister af (bv_xor (extract (bv_xor v_4361 v_4365) 11 12) (extract v_4367 12 13));
      setRegister zf (zeroFlag v_4370);
      setRegister sf v_4369;
      setRegister cf (extract v_4367 0 1);
      pure ()
    pat_end;
    pattern fun (v_2503 : Mem) (v_2504 : reg (bv 16)) => do
      v_8962 <- getRegister cf;
      v_8964 <- evaluateAddress v_2503;
      v_8965 <- load v_8964 2;
      v_8966 <- eval (concat (expression.bv_nat 1 0) v_8965);
      v_8969 <- getRegister v_2504;
      v_8971 <- eval (add (mux (eq v_8962 (expression.bv_nat 1 1)) (add v_8966 (expression.bv_nat 17 1)) v_8966) (concat (expression.bv_nat 1 0) v_8969));
      v_8973 <- eval (extract v_8971 1 2);
      v_8978 <- eval (extract v_8971 1 17);
      v_8983 <- eval (eq (extract v_8965 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2504) v_8978;
      setRegister of (mux (bit_and (eq v_8983 (eq (extract v_8969 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8983 (eq v_8973 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8971 9 17));
      setRegister zf (zeroFlag v_8978);
      setRegister af (bv_xor (extract (bv_xor v_8965 v_8969) 11 12) (extract v_8971 12 13));
      setRegister sf v_8973;
      setRegister cf (extract v_8971 0 1);
      pure ()
    pat_end;
    pattern fun (v_2491 : imm int) (v_2490 : Mem) => do
      v_10498 <- evaluateAddress v_2490;
      v_10499 <- getRegister cf;
      v_10501 <- eval (handleImmediateWithSignExtend v_2491 16 16);
      v_10502 <- eval (concat (expression.bv_nat 1 0) v_10501);
      v_10505 <- load v_10498 2;
      v_10507 <- eval (add (mux (eq v_10499 (expression.bv_nat 1 1)) (add v_10502 (expression.bv_nat 17 1)) v_10502) (concat (expression.bv_nat 1 0) v_10505));
      v_10508 <- eval (extract v_10507 1 17);
      store v_10498 v_10508 2;
      v_10511 <- eval (extract v_10507 1 2);
      v_10520 <- eval (eq (extract v_10501 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10520 (eq (extract v_10505 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10520 (eq v_10511 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10507 9 17));
      setRegister af (bv_xor (extract (bv_xor v_10501 v_10505) 11 12) (extract v_10507 12 13));
      setRegister zf (zeroFlag v_10508);
      setRegister sf v_10511;
      setRegister cf (extract v_10507 0 1);
      pure ()
    pat_end;
    pattern fun (v_2495 : reg (bv 16)) (v_2494 : Mem) => do
      v_10535 <- evaluateAddress v_2494;
      v_10536 <- getRegister cf;
      v_10538 <- getRegister v_2495;
      v_10539 <- eval (concat (expression.bv_nat 1 0) v_10538);
      v_10542 <- load v_10535 2;
      v_10544 <- eval (add (mux (eq v_10536 (expression.bv_nat 1 1)) (add v_10539 (expression.bv_nat 17 1)) v_10539) (concat (expression.bv_nat 1 0) v_10542));
      v_10545 <- eval (extract v_10544 1 17);
      store v_10535 v_10545 2;
      v_10548 <- eval (extract v_10544 1 2);
      v_10557 <- eval (eq (extract v_10538 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10557 (eq (extract v_10542 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10557 (eq v_10548 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10544 9 17));
      setRegister af (bv_xor (extract (bv_xor v_10538 v_10542) 11 12) (extract v_10544 12 13));
      setRegister zf (zeroFlag v_10545);
      setRegister sf v_10548;
      setRegister cf (extract v_10544 0 1);
      pure ()
    pat_end
