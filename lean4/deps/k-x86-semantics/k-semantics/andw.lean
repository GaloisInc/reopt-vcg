def andw1 : instruction :=
  definst "andw" $ do
    pattern fun (v_2862 : imm int) ax => do
      v_5609 <- getRegister rax;
      v_5611 <- eval (handleImmediateWithSignExtend v_2862 16 16);
      v_5615 <- eval (bv_and (extract v_5609 48 64) v_5611);
      setRegister rax (concat (extract v_5609 0 48) v_5615);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_and (extract v_5609 63 64) (extract v_5611 15 16)) (expression.bv_nat 1 1)) (eq (bv_and (extract v_5609 62 63) (extract v_5611 14 15)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5609 61 62) (extract v_5611 13 14)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5609 60 61) (extract v_5611 12 13)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5609 59 60) (extract v_5611 11 12)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5609 58 59) (extract v_5611 10 11)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5609 57 58) (extract v_5611 9 10)) (expression.bv_nat 1 1)))) (eq (bv_and (extract v_5609 56 57) (extract v_5611 8 9)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5615);
      setRegister af undef;
      setRegister sf (bv_and (extract v_5609 48 49) (extract v_5611 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2874 : imm int) (v_2876 : reg (bv 16)) => do
      v_5680 <- getRegister v_2876;
      v_5682 <- eval (bv_and v_5680 (handleImmediateWithSignExtend v_2874 16 16));
      setRegister (lhs.of_reg v_2876) v_5682;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5682 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_5682);
      setRegister sf (extract v_5682 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2884 : reg (bv 16)) (v_2885 : reg (bv 16)) => do
      v_5698 <- getRegister v_2885;
      v_5699 <- getRegister v_2884;
      v_5700 <- eval (bv_and v_5698 v_5699);
      setRegister (lhs.of_reg v_2885) v_5700;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5700 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_5700);
      setRegister sf (extract v_5700 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2879 : Mem) (v_2880 : reg (bv 16)) => do
      v_9426 <- getRegister v_2880;
      v_9427 <- evaluateAddress v_2879;
      v_9428 <- load v_9427 2;
      v_9429 <- eval (bv_and v_9426 v_9428);
      setRegister (lhs.of_reg v_2880) v_9429;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9429 8 16));
      setRegister zf (zeroFlag v_9429);
      setRegister af undef;
      setRegister sf (extract v_9429 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2867 : imm int) (v_2866 : Mem) => do
      v_11020 <- evaluateAddress v_2866;
      v_11021 <- load v_11020 2;
      v_11023 <- eval (bv_and v_11021 (handleImmediateWithSignExtend v_2867 16 16));
      store v_11020 v_11023 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11023 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_11023);
      setRegister sf (extract v_11023 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2871 : reg (bv 16)) (v_2870 : Mem) => do
      v_11035 <- evaluateAddress v_2870;
      v_11036 <- load v_11035 2;
      v_11037 <- getRegister v_2871;
      v_11038 <- eval (bv_and v_11036 v_11037);
      store v_11035 v_11038 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11038 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_11038);
      setRegister sf (extract v_11038 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
