def orb1 : instruction :=
  definst "orb" $ do
    pattern fun (v_2906 : imm int) al => do
      v_4630 <- getRegister rax;
      v_4632 <- eval (handleImmediateWithSignExtend v_2906 8 8);
      v_4634 <- eval (bv_or (extract v_4630 56 57) (extract v_4632 0 1));
      v_4636 <- eval (bv_or (extract v_4630 56 64) v_4632);
      setRegister rax (concat (extract v_4630 0 56) v_4636);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4630 63 64) (extract v_4632 7 8)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4630 62 63) (extract v_4632 6 7)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4630 61 62) (extract v_4632 5 6)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4630 60 61) (extract v_4632 4 5)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4630 59 60) (extract v_4632 3 4)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4630 58 59) (extract v_4632 2 3)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4630 57 58) (extract v_4632 1 2)) (expression.bv_nat 1 1)))) (eq v_4634 (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4636);
      setRegister af undef;
      setRegister sf v_4634;
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2922 : imm int) (v_2923 : reg (bv 8)) => do
      v_4702 <- getRegister v_2923;
      v_4704 <- eval (bv_or v_4702 (handleImmediateWithSignExtend v_2922 8 8));
      setRegister (lhs.of_reg v_2923) v_4704;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4704 0 8));
      setRegister zf (zeroFlag v_4704);
      setRegister af undef;
      setRegister sf (extract v_4704 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2931 : reg (bv 8)) (v_2932 : reg (bv 8)) => do
      v_4720 <- getRegister v_2932;
      v_4721 <- getRegister v_2931;
      v_4722 <- eval (bv_or v_4720 v_4721);
      setRegister (lhs.of_reg v_2932) v_4722;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4722 0 8));
      setRegister zf (zeroFlag v_4722);
      setRegister af undef;
      setRegister sf (extract v_4722 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2941 : imm int) (v_2942 : reg (bv 8)) => do
      v_4748 <- getRegister v_2942;
      v_4750 <- eval (bv_or v_4748 (handleImmediateWithSignExtend v_2941 8 8));
      setRegister (lhs.of_reg v_2942) v_4750;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4750 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_4750);
      setRegister sf (extract v_4750 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2950 : reg (bv 8)) (v_2951 : reg (bv 8)) => do
      v_4766 <- getRegister v_2951;
      v_4767 <- getRegister v_2950;
      v_4768 <- eval (bv_or v_4766 v_4767);
      setRegister (lhs.of_reg v_2951) v_4768;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4768 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_4768);
      setRegister sf (extract v_4768 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2927 : Mem) (v_2928 : reg (bv 8)) => do
      v_9176 <- getRegister v_2928;
      v_9177 <- evaluateAddress v_2927;
      v_9178 <- load v_9177 1;
      v_9179 <- eval (bv_or v_9176 v_9178);
      setRegister (lhs.of_reg v_2928) v_9179;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9179 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_9179);
      setRegister sf (extract v_9179 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2911 : imm int) (v_2910 : Mem) => do
      v_11114 <- evaluateAddress v_2910;
      v_11115 <- load v_11114 1;
      v_11117 <- eval (bv_or v_11115 (handleImmediateWithSignExtend v_2911 8 8));
      store v_11114 v_11117 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11117 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_11117);
      setRegister sf (extract v_11117 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2915 : reg (bv 8)) (v_2914 : Mem) => do
      v_11129 <- evaluateAddress v_2914;
      v_11130 <- load v_11129 1;
      v_11131 <- getRegister v_2915;
      v_11132 <- eval (bv_or v_11130 v_11131);
      store v_11129 v_11132 1;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11132 0 8));
      setRegister af undef;
      setRegister zf (zeroFlag v_11132);
      setRegister sf (extract v_11132 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
