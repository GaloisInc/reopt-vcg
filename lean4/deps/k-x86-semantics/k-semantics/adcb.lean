def adcb1 : instruction :=
  definst "adcb" $ do
    pattern fun (v_2393 : imm int) al => do
      v_3767 <- getRegister cf;
      v_3769 <- eval (handleImmediateWithSignExtend v_2393 8 8);
      v_3770 <- eval (concat (expression.bv_nat 1 0) v_3769);
      v_3773 <- getRegister rax;
      v_3776 <- eval (add (mux (eq v_3767 (expression.bv_nat 1 1)) (add v_3770 (expression.bv_nat 9 1)) v_3770) (concat (expression.bv_nat 1 0) (extract v_3773 56 64)));
      v_3778 <- eval (extract v_3776 1 2);
      v_3784 <- eval (extract v_3776 1 9);
      v_3788 <- eval (eq (extract v_3769 0 1) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_3773 0 56) v_3784);
      setRegister of (mux (bit_and (eq v_3788 (eq (extract v_3773 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_3788 (eq v_3778 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3784);
      setRegister zf (zeroFlag v_3784);
      setRegister af (bv_xor (bv_xor (extract v_3769 3 4) (extract v_3773 59 60)) (extract v_3776 4 5));
      setRegister sf v_3778;
      setRegister cf (extract v_3776 0 1);
      pure ()
    pat_end;
    pattern fun (v_2409 : imm int) (v_2411 : reg (bv 8)) => do
      v_3818 <- getRegister cf;
      v_3820 <- eval (handleImmediateWithSignExtend v_2409 8 8);
      v_3821 <- eval (concat (expression.bv_nat 1 0) v_3820);
      v_3824 <- getRegister v_2411;
      v_3826 <- eval (add (mux (eq v_3818 (expression.bv_nat 1 1)) (add v_3821 (expression.bv_nat 9 1)) v_3821) (concat (expression.bv_nat 1 0) v_3824));
      v_3828 <- eval (extract v_3826 1 2);
      v_3833 <- eval (extract v_3826 1 9);
      v_3837 <- eval (eq (extract v_3820 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2411) v_3833;
      setRegister of (mux (bit_and (eq v_3837 (eq (extract v_3824 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3837 (eq v_3828 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3833);
      setRegister zf (zeroFlag v_3833);
      setRegister af (bv_xor (extract (bv_xor v_3820 v_3824) 3 4) (extract v_3826 4 5));
      setRegister sf v_3828;
      setRegister cf (extract v_3826 0 1);
      pure ()
    pat_end;
    pattern fun (v_2419 : reg (bv 8)) (v_2420 : reg (bv 8)) => do
      v_3857 <- getRegister cf;
      v_3859 <- getRegister v_2419;
      v_3860 <- eval (concat (expression.bv_nat 1 0) v_3859);
      v_3863 <- getRegister v_2420;
      v_3865 <- eval (add (mux (eq v_3857 (expression.bv_nat 1 1)) (add v_3860 (expression.bv_nat 9 1)) v_3860) (concat (expression.bv_nat 1 0) v_3863));
      v_3867 <- eval (extract v_3865 1 2);
      v_3872 <- eval (extract v_3865 1 9);
      v_3876 <- eval (eq (extract v_3859 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2420) v_3872;
      setRegister of (mux (bit_and (eq v_3876 (eq (extract v_3863 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3876 (eq v_3867 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3872);
      setRegister zf (zeroFlag v_3872);
      setRegister af (bv_xor (extract (bv_xor v_3859 v_3863) 3 4) (extract v_3865 4 5));
      setRegister sf v_3867;
      setRegister cf (extract v_3865 0 1);
      pure ()
    pat_end;
    pattern fun (v_2428 : imm int) (v_2430 : reg (bv 8)) => do
      v_3927 <- getRegister cf;
      v_3929 <- eval (handleImmediateWithSignExtend v_2428 8 8);
      v_3930 <- eval (concat (expression.bv_nat 1 0) v_3929);
      v_3933 <- getRegister v_2430;
      v_3935 <- eval (add (mux (eq v_3927 (expression.bv_nat 1 1)) (add v_3930 (expression.bv_nat 9 1)) v_3930) (concat (expression.bv_nat 1 0) v_3933));
      v_3937 <- eval (extract v_3935 1 2);
      v_3938 <- eval (extract v_3935 1 9);
      v_3946 <- eval (eq (extract v_3929 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2430) v_3938;
      setRegister of (mux (bit_and (eq v_3946 (eq (extract v_3933 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3946 (eq v_3937 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3938);
      setRegister af (bv_xor (extract (bv_xor v_3929 v_3933) 3 4) (extract v_3935 4 5));
      setRegister zf (zeroFlag v_3938);
      setRegister sf v_3937;
      setRegister cf (extract v_3935 0 1);
      pure ()
    pat_end;
    pattern fun (v_2439 : reg (bv 8)) (v_2438 : reg (bv 8)) => do
      v_3966 <- getRegister cf;
      v_3968 <- getRegister v_2439;
      v_3969 <- eval (concat (expression.bv_nat 1 0) v_3968);
      v_3972 <- getRegister v_2438;
      v_3974 <- eval (add (mux (eq v_3966 (expression.bv_nat 1 1)) (add v_3969 (expression.bv_nat 9 1)) v_3969) (concat (expression.bv_nat 1 0) v_3972));
      v_3976 <- eval (extract v_3974 1 2);
      v_3977 <- eval (extract v_3974 1 9);
      v_3985 <- eval (eq (extract v_3968 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2438) v_3977;
      setRegister of (mux (bit_and (eq v_3985 (eq (extract v_3972 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3985 (eq v_3976 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_3977);
      setRegister af (bv_xor (extract (bv_xor v_3968 v_3972) 3 4) (extract v_3974 4 5));
      setRegister zf (zeroFlag v_3977);
      setRegister sf v_3976;
      setRegister cf (extract v_3974 0 1);
      pure ()
    pat_end;
    pattern fun (v_2414 : Mem) (v_2415 : reg (bv 8)) => do
      v_8950 <- getRegister cf;
      v_8952 <- evaluateAddress v_2414;
      v_8953 <- load v_8952 1;
      v_8954 <- eval (concat (expression.bv_nat 1 0) v_8953);
      v_8957 <- getRegister v_2415;
      v_8959 <- eval (add (mux (eq v_8950 (expression.bv_nat 1 1)) (add v_8954 (expression.bv_nat 9 1)) v_8954) (concat (expression.bv_nat 1 0) v_8957));
      v_8961 <- eval (extract v_8959 1 2);
      v_8966 <- eval (extract v_8959 1 9);
      v_8970 <- eval (eq (extract v_8953 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2415) v_8966;
      setRegister of (mux (bit_and (eq v_8970 (eq (extract v_8957 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8970 (eq v_8961 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8966);
      setRegister zf (zeroFlag v_8966);
      setRegister af (bv_xor (extract (bv_xor v_8953 v_8957) 3 4) (extract v_8959 4 5));
      setRegister sf v_8961;
      setRegister cf (extract v_8959 0 1);
      pure ()
    pat_end;
    pattern fun (v_2398 : imm int) (v_2397 : Mem) => do
      v_10525 <- evaluateAddress v_2397;
      v_10526 <- getRegister cf;
      v_10528 <- eval (handleImmediateWithSignExtend v_2398 8 8);
      v_10529 <- eval (concat (expression.bv_nat 1 0) v_10528);
      v_10532 <- load v_10525 1;
      v_10534 <- eval (add (mux (eq v_10526 (expression.bv_nat 1 1)) (add v_10529 (expression.bv_nat 9 1)) v_10529) (concat (expression.bv_nat 1 0) v_10532));
      v_10535 <- eval (extract v_10534 1 9);
      store v_10525 v_10535 1;
      v_10538 <- eval (extract v_10534 1 2);
      v_10546 <- eval (eq (extract v_10528 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10546 (eq (extract v_10532 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10546 (eq v_10538 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10535);
      setRegister af (bv_xor (extract (bv_xor v_10528 v_10532) 3 4) (extract v_10534 4 5));
      setRegister zf (zeroFlag v_10535);
      setRegister sf v_10538;
      setRegister cf (extract v_10534 0 1);
      pure ()
    pat_end;
    pattern fun (v_2402 : reg (bv 8)) (v_2401 : Mem) => do
      v_10561 <- evaluateAddress v_2401;
      v_10562 <- getRegister cf;
      v_10564 <- getRegister v_2402;
      v_10565 <- eval (concat (expression.bv_nat 1 0) v_10564);
      v_10568 <- load v_10561 1;
      v_10570 <- eval (add (mux (eq v_10562 (expression.bv_nat 1 1)) (add v_10565 (expression.bv_nat 9 1)) v_10565) (concat (expression.bv_nat 1 0) v_10568));
      v_10571 <- eval (extract v_10570 1 9);
      store v_10561 v_10571 1;
      v_10574 <- eval (extract v_10570 1 2);
      v_10582 <- eval (eq (extract v_10564 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10582 (eq (extract v_10568 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10582 (eq v_10574 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_10571);
      setRegister af (bv_xor (extract (bv_xor v_10564 v_10568) 3 4) (extract v_10570 4 5));
      setRegister zf (zeroFlag v_10571);
      setRegister sf v_10574;
      setRegister cf (extract v_10570 0 1);
      pure ()
    pat_end
