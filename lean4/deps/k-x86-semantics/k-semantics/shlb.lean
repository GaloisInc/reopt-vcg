def shlb1 : instruction :=
  definst "shlb" $ do
    pattern fun cl (v_2720 : reg (bv 8)) => do
      v_4302 <- getRegister rcx;
      v_4304 <- eval (bv_and (extract v_4302 56 64) (expression.bv_nat 8 31));
      v_4305 <- eval (uge v_4304 (expression.bv_nat 8 8));
      v_4308 <- eval (eq v_4304 (expression.bv_nat 8 0));
      v_4309 <- eval (notBool_ v_4308);
      v_4310 <- getRegister v_2720;
      v_4311 <- eval (concat (expression.bv_nat 1 0) v_4310);
      v_4316 <- eval (extract (shl v_4311 (uvalueMInt (concat (expression.bv_nat 1 0) v_4304))) 0 (bitwidthMInt v_4311));
      v_4320 <- getRegister cf;
      v_4325 <- eval (bit_or (bit_and v_4305 undef) (bit_and (notBool_ v_4305) (bit_or (bit_and v_4309 (eq (extract v_4316 0 1) (expression.bv_nat 1 1))) (bit_and v_4308 (eq v_4320 (expression.bv_nat 1 1))))));
      v_4328 <- eval (eq (extract v_4316 1 2) (expression.bv_nat 1 1));
      v_4330 <- getRegister sf;
      v_4335 <- eval (extract v_4316 1 9);
      v_4338 <- getRegister zf;
      v_4343 <- eval (bit_and v_4309 undef);
      v_4344 <- getRegister af;
      v_4377 <- getRegister pf;
      v_4382 <- eval (eq v_4304 (expression.bv_nat 8 1));
      v_4387 <- getRegister of;
      setRegister (lhs.of_reg v_2720) v_4335;
      setRegister of (mux (bit_or (bit_and v_4382 (notBool_ (eq v_4325 v_4328))) (bit_and (notBool_ v_4382) (bit_or v_4343 (bit_and v_4308 (eq v_4387 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4309 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4316 8 9) (expression.bv_nat 1 1)) (eq (extract v_4316 7 8) (expression.bv_nat 1 1)))) (eq (extract v_4316 6 7) (expression.bv_nat 1 1)))) (eq (extract v_4316 5 6) (expression.bv_nat 1 1)))) (eq (extract v_4316 4 5) (expression.bv_nat 1 1)))) (eq (extract v_4316 3 4) (expression.bv_nat 1 1)))) (eq (extract v_4316 2 3) (expression.bv_nat 1 1)))) v_4328)) (bit_and v_4308 (eq v_4377 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_4343 (bit_and v_4308 (eq v_4344 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4309 (eq v_4335 (expression.bv_nat 8 0))) (bit_and v_4308 (eq v_4338 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4309 v_4328) (bit_and v_4308 (eq v_4330 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_4325 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2723 : imm int) (v_2725 : reg (bv 8)) => do
      v_4402 <- eval (bv_and (handleImmediateWithSignExtend v_2723 8 8) (expression.bv_nat 8 31));
      v_4403 <- eval (uge v_4402 (expression.bv_nat 8 8));
      v_4406 <- eval (eq v_4402 (expression.bv_nat 8 0));
      v_4407 <- eval (notBool_ v_4406);
      v_4408 <- getRegister v_2725;
      v_4409 <- eval (concat (expression.bv_nat 1 0) v_4408);
      v_4414 <- eval (extract (shl v_4409 (uvalueMInt (concat (expression.bv_nat 1 0) v_4402))) 0 (bitwidthMInt v_4409));
      v_4418 <- getRegister cf;
      v_4423 <- eval (bit_or (bit_and v_4403 undef) (bit_and (notBool_ v_4403) (bit_or (bit_and v_4407 (eq (extract v_4414 0 1) (expression.bv_nat 1 1))) (bit_and v_4406 (eq v_4418 (expression.bv_nat 1 1))))));
      v_4426 <- eval (eq (extract v_4414 1 2) (expression.bv_nat 1 1));
      v_4428 <- getRegister sf;
      v_4433 <- eval (extract v_4414 1 9);
      v_4436 <- getRegister zf;
      v_4441 <- eval (bit_and v_4407 undef);
      v_4442 <- getRegister af;
      v_4475 <- getRegister pf;
      v_4480 <- eval (eq v_4402 (expression.bv_nat 8 1));
      v_4485 <- getRegister of;
      setRegister (lhs.of_reg v_2725) v_4433;
      setRegister of (mux (bit_or (bit_and v_4480 (notBool_ (eq v_4423 v_4426))) (bit_and (notBool_ v_4480) (bit_or v_4441 (bit_and v_4406 (eq v_4485 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_4407 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4414 8 9) (expression.bv_nat 1 1)) (eq (extract v_4414 7 8) (expression.bv_nat 1 1)))) (eq (extract v_4414 6 7) (expression.bv_nat 1 1)))) (eq (extract v_4414 5 6) (expression.bv_nat 1 1)))) (eq (extract v_4414 4 5) (expression.bv_nat 1 1)))) (eq (extract v_4414 3 4) (expression.bv_nat 1 1)))) (eq (extract v_4414 2 3) (expression.bv_nat 1 1)))) v_4426)) (bit_and v_4406 (eq v_4475 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_4441 (bit_and v_4406 (eq v_4442 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_4407 (eq v_4433 (expression.bv_nat 8 0))) (bit_and v_4406 (eq v_4436 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_4407 v_4426) (bit_and v_4406 (eq v_4428 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_4423 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2729 : reg (bv 8)) => do
      v_4499 <- getRegister v_2729;
      v_4500 <- eval (concat (expression.bv_nat 1 0) v_4499);
      v_4503 <- eval (extract (shl v_4500 1) 0 (bitwidthMInt v_4500));
      v_4504 <- eval (extract v_4503 0 1);
      v_4505 <- eval (extract v_4503 1 2);
      v_4506 <- eval (extract v_4503 1 9);
      setRegister (lhs.of_reg v_2729) v_4506;
      setRegister of (mux (notBool_ (eq (eq v_4504 (expression.bv_nat 1 1)) (eq v_4505 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_4506);
      setRegister af undef;
      setRegister zf (zeroFlag v_4506);
      setRegister sf v_4505;
      setRegister cf v_4504;
      pure ()
    pat_end;
    pattern fun cl (v_2709 : Mem) => do
      v_10577 <- evaluateAddress v_2709;
      v_10578 <- load v_10577 1;
      v_10579 <- eval (concat (expression.bv_nat 1 0) v_10578);
      v_10580 <- getRegister rcx;
      v_10582 <- eval (bv_and (extract v_10580 56 64) (expression.bv_nat 8 31));
      v_10587 <- eval (extract (shl v_10579 (uvalueMInt (concat (expression.bv_nat 1 0) v_10582))) 0 (bitwidthMInt v_10579));
      v_10588 <- eval (extract v_10587 1 9);
      store v_10577 v_10588 1;
      v_10590 <- eval (uge v_10582 (expression.bv_nat 8 8));
      v_10593 <- eval (eq v_10582 (expression.bv_nat 8 0));
      v_10594 <- eval (notBool_ v_10593);
      v_10598 <- getRegister cf;
      v_10603 <- eval (bit_or (bit_and v_10590 undef) (bit_and (notBool_ v_10590) (bit_or (bit_and v_10594 (eq (extract v_10587 0 1) (expression.bv_nat 1 1))) (bit_and v_10593 (eq v_10598 (expression.bv_nat 1 1))))));
      v_10606 <- eval (eq (extract v_10587 1 2) (expression.bv_nat 1 1));
      v_10608 <- getRegister sf;
      v_10615 <- getRegister zf;
      v_10620 <- eval (bit_and v_10594 undef);
      v_10621 <- getRegister af;
      v_10654 <- getRegister pf;
      v_10659 <- eval (eq v_10582 (expression.bv_nat 8 1));
      v_10664 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_10659 (notBool_ (eq v_10603 v_10606))) (bit_and (notBool_ v_10659) (bit_or v_10620 (bit_and v_10593 (eq v_10664 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_10594 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_10587 8 9) (expression.bv_nat 1 1)) (eq (extract v_10587 7 8) (expression.bv_nat 1 1)))) (eq (extract v_10587 6 7) (expression.bv_nat 1 1)))) (eq (extract v_10587 5 6) (expression.bv_nat 1 1)))) (eq (extract v_10587 4 5) (expression.bv_nat 1 1)))) (eq (extract v_10587 3 4) (expression.bv_nat 1 1)))) (eq (extract v_10587 2 3) (expression.bv_nat 1 1)))) v_10606)) (bit_and v_10593 (eq v_10654 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_10620 (bit_and v_10593 (eq v_10621 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_10594 (eq v_10588 (expression.bv_nat 8 0))) (bit_and v_10593 (eq v_10615 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_10594 v_10606) (bit_and v_10593 (eq v_10608 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_10603 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2712 : imm int) (v_2713 : Mem) => do
      v_10677 <- evaluateAddress v_2713;
      v_10678 <- load v_10677 1;
      v_10679 <- eval (concat (expression.bv_nat 1 0) v_10678);
      v_10681 <- eval (bv_and (handleImmediateWithSignExtend v_2712 8 8) (expression.bv_nat 8 31));
      v_10686 <- eval (extract (shl v_10679 (uvalueMInt (concat (expression.bv_nat 1 0) v_10681))) 0 (bitwidthMInt v_10679));
      v_10687 <- eval (extract v_10686 1 9);
      store v_10677 v_10687 1;
      v_10689 <- eval (uge v_10681 (expression.bv_nat 8 8));
      v_10692 <- eval (eq v_10681 (expression.bv_nat 8 0));
      v_10693 <- eval (notBool_ v_10692);
      v_10697 <- getRegister cf;
      v_10702 <- eval (bit_or (bit_and v_10689 undef) (bit_and (notBool_ v_10689) (bit_or (bit_and v_10693 (eq (extract v_10686 0 1) (expression.bv_nat 1 1))) (bit_and v_10692 (eq v_10697 (expression.bv_nat 1 1))))));
      v_10705 <- eval (eq (extract v_10686 1 2) (expression.bv_nat 1 1));
      v_10707 <- getRegister sf;
      v_10714 <- getRegister zf;
      v_10719 <- eval (bit_and v_10693 undef);
      v_10720 <- getRegister af;
      v_10753 <- getRegister pf;
      v_10758 <- eval (eq v_10681 (expression.bv_nat 8 1));
      v_10763 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_10758 (notBool_ (eq v_10702 v_10705))) (bit_and (notBool_ v_10758) (bit_or v_10719 (bit_and v_10692 (eq v_10763 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_10693 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_10686 8 9) (expression.bv_nat 1 1)) (eq (extract v_10686 7 8) (expression.bv_nat 1 1)))) (eq (extract v_10686 6 7) (expression.bv_nat 1 1)))) (eq (extract v_10686 5 6) (expression.bv_nat 1 1)))) (eq (extract v_10686 4 5) (expression.bv_nat 1 1)))) (eq (extract v_10686 3 4) (expression.bv_nat 1 1)))) (eq (extract v_10686 2 3) (expression.bv_nat 1 1)))) v_10705)) (bit_and v_10692 (eq v_10753 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_10719 (bit_and v_10692 (eq v_10720 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_10693 (eq v_10687 (expression.bv_nat 8 0))) (bit_and v_10692 (eq v_10714 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_10693 v_10705) (bit_and v_10692 (eq v_10707 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_10702 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
