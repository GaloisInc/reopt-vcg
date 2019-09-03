def orb1 : instruction :=
  definst "orb" $ do
    pattern fun (v_2893 : imm int) al => do
      v_4541 <- getRegister rax;
      v_4543 <- eval (handleImmediateWithSignExtend v_2893 8 8);
      v_4545 <- eval (bv_or (extract v_4541 56 57) (extract v_4543 0 1));
      v_4547 <- eval (bv_or (extract v_4541 56 64) v_4543);
      setRegister rax (concat (extract v_4541 0 56) v_4547);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4541 63 64) (extract v_4543 7 8)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4541 62 63) (extract v_4543 6 7)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4541 61 62) (extract v_4543 5 6)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4541 60 61) (extract v_4543 4 5)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4541 59 60) (extract v_4543 3 4)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4541 58 59) (extract v_4543 2 3)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4541 57 58) (extract v_4543 1 2)) (expression.bv_nat 1 1)))) (eq v_4545 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4547);
      setRegister af undef;
      setRegister sf v_4545;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2909 : imm int) (v_2911 : reg (bv 8)) => do
      v_4613 <- getRegister v_2911;
      v_4615 <- eval (bv_or v_4613 (handleImmediateWithSignExtend v_2909 8 8));
      setRegister (lhs.of_reg v_2911) v_4615;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4615 0 8));
      setRegister zf (zeroFlag v_4615);
      setRegister af undef;
      setRegister sf (extract v_4615 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2919 : reg (bv 8)) (v_2920 : reg (bv 8)) => do
      v_4631 <- getRegister v_2920;
      v_4632 <- getRegister v_2919;
      v_4633 <- eval (bv_or v_4631 v_4632);
      setRegister (lhs.of_reg v_2920) v_4633;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4633 0 8));
      setRegister zf (zeroFlag v_4633);
      setRegister af undef;
      setRegister sf (extract v_4633 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2914 : Mem) (v_2915 : reg (bv 8)) => do
      v_9101 <- getRegister v_2915;
      v_9102 <- evaluateAddress v_2914;
      v_9103 <- load v_9102 1;
      v_9104 <- eval (bv_or v_9101 v_9103);
      setRegister (lhs.of_reg v_2915) v_9104;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9104 0 8));
      setRegister zf (zeroFlag v_9104);
      setRegister af undef;
      setRegister sf (extract v_9104 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2898 : imm int) (v_2897 : Mem) => do
      v_11162 <- evaluateAddress v_2897;
      v_11163 <- load v_11162 1;
      v_11165 <- eval (bv_or v_11163 (handleImmediateWithSignExtend v_2898 8 8));
      store v_11162 v_11165 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11165 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_11165);
      setRegister sf (extract v_11165 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2902 : reg (bv 8)) (v_2901 : Mem) => do
      v_11177 <- evaluateAddress v_2901;
      v_11178 <- load v_11177 1;
      v_11179 <- getRegister v_2902;
      v_11180 <- eval (bv_or v_11178 v_11179);
      store v_11177 v_11180 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11180 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_11180);
      setRegister sf (extract v_11180 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
