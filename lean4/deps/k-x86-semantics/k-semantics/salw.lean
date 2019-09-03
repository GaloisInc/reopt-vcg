def salw1 : instruction :=
  definst "salw" $ do
    pattern fun cl (v_2994 : reg (bv 16)) => do
      v_6823 <- getRegister rcx;
      v_6825 <- eval (bv_and (extract v_6823 56 64) (expression.bv_nat 8 31));
      v_6826 <- eval (uge v_6825 (expression.bv_nat 8 16));
      v_6829 <- eval (eq v_6825 (expression.bv_nat 8 0));
      v_6830 <- eval (notBool_ v_6829);
      v_6831 <- getRegister v_2994;
      v_6836 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6831) (uvalueMInt (concat (expression.bv_nat 9 0) v_6825))) 0 17);
      v_6840 <- getRegister cf;
      v_6845 <- eval (bit_or (bit_and v_6826 undef) (bit_and (notBool_ v_6826) (bit_or (bit_and v_6830 (eq (extract v_6836 0 1) (expression.bv_nat 1 1))) (bit_and v_6829 (eq v_6840 (expression.bv_nat 1 1))))));
      v_6848 <- eval (eq (extract v_6836 1 2) (expression.bv_nat 1 1));
      v_6850 <- getRegister sf;
      v_6855 <- eval (bit_and v_6830 undef);
      v_6856 <- getRegister af;
      v_6861 <- eval (extract v_6836 1 17);
      v_6864 <- getRegister zf;
      v_6899 <- getRegister pf;
      v_6904 <- eval (eq v_6825 (expression.bv_nat 8 1));
      v_6909 <- getRegister of;
      setRegister (lhs.of_reg v_2994) v_6861;
      setRegister of (mux (bit_or (bit_and v_6904 (notBool_ (eq v_6845 v_6848))) (bit_and (notBool_ v_6904) (bit_or v_6855 (bit_and v_6829 (eq v_6909 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6830 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6836 16 17) (expression.bv_nat 1 1)) (eq (extract v_6836 15 16) (expression.bv_nat 1 1)))) (eq (extract v_6836 14 15) (expression.bv_nat 1 1)))) (eq (extract v_6836 13 14) (expression.bv_nat 1 1)))) (eq (extract v_6836 12 13) (expression.bv_nat 1 1)))) (eq (extract v_6836 11 12) (expression.bv_nat 1 1)))) (eq (extract v_6836 10 11) (expression.bv_nat 1 1)))) (eq (extract v_6836 9 10) (expression.bv_nat 1 1)))) (bit_and v_6829 (eq v_6899 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6830 (eq v_6861 (expression.bv_nat 16 0))) (bit_and v_6829 (eq v_6864 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6855 (bit_and v_6829 (eq v_6856 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6830 v_6848) (bit_and v_6829 (eq v_6850 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6845 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2997 : imm int) (v_2999 : reg (bv 16)) => do
      v_6924 <- eval (bv_and (handleImmediateWithSignExtend v_2997 8 8) (expression.bv_nat 8 31));
      v_6925 <- eval (uge v_6924 (expression.bv_nat 8 16));
      v_6928 <- eval (eq v_6924 (expression.bv_nat 8 0));
      v_6929 <- eval (notBool_ v_6928);
      v_6930 <- getRegister v_2999;
      v_6935 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_6930) (uvalueMInt (concat (expression.bv_nat 9 0) v_6924))) 0 17);
      v_6939 <- getRegister cf;
      v_6944 <- eval (bit_or (bit_and v_6925 undef) (bit_and (notBool_ v_6925) (bit_or (bit_and v_6929 (eq (extract v_6935 0 1) (expression.bv_nat 1 1))) (bit_and v_6928 (eq v_6939 (expression.bv_nat 1 1))))));
      v_6947 <- eval (eq (extract v_6935 1 2) (expression.bv_nat 1 1));
      v_6949 <- getRegister sf;
      v_6954 <- eval (bit_and v_6929 undef);
      v_6955 <- getRegister af;
      v_6960 <- eval (extract v_6935 1 17);
      v_6963 <- getRegister zf;
      v_6998 <- getRegister pf;
      v_7003 <- eval (eq v_6924 (expression.bv_nat 8 1));
      v_7008 <- getRegister of;
      setRegister (lhs.of_reg v_2999) v_6960;
      setRegister of (mux (bit_or (bit_and v_7003 (notBool_ (eq v_6944 v_6947))) (bit_and (notBool_ v_7003) (bit_or v_6954 (bit_and v_6928 (eq v_7008 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6929 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6935 16 17) (expression.bv_nat 1 1)) (eq (extract v_6935 15 16) (expression.bv_nat 1 1)))) (eq (extract v_6935 14 15) (expression.bv_nat 1 1)))) (eq (extract v_6935 13 14) (expression.bv_nat 1 1)))) (eq (extract v_6935 12 13) (expression.bv_nat 1 1)))) (eq (extract v_6935 11 12) (expression.bv_nat 1 1)))) (eq (extract v_6935 10 11) (expression.bv_nat 1 1)))) (eq (extract v_6935 9 10) (expression.bv_nat 1 1)))) (bit_and v_6928 (eq v_6998 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6929 (eq v_6960 (expression.bv_nat 16 0))) (bit_and v_6928 (eq v_6963 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6954 (bit_and v_6928 (eq v_6955 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6929 v_6947) (bit_and v_6928 (eq v_6949 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_6944 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_3006 : reg (bv 16)) => do
      v_7024 <- getRegister v_3006;
      v_7027 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_7024) 1) 0 17);
      v_7028 <- eval (extract v_7027 0 1);
      v_7029 <- eval (extract v_7027 1 2);
      v_7030 <- eval (extract v_7027 1 17);
      setRegister (lhs.of_reg v_3006) v_7030;
      setRegister of (mux (notBool_ (eq (eq v_7028 (expression.bv_nat 1 1)) (eq v_7029 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7027 9 17));
      setRegister zf (zeroFlag v_7030);
      setRegister af undef;
      setRegister sf v_7029;
      setRegister cf v_7028;
      pure ()
    pat_end;
    pattern fun (v_3002 : reg (bv 16)) => do
      v_9579 <- getRegister v_3002;
      v_9582 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9579) 1) 0 17);
      v_9584 <- eval (eq (extract v_9582 0 1) (expression.bv_nat 1 1));
      v_9587 <- eval (eq (extract v_9582 1 2) (expression.bv_nat 1 1));
      v_9589 <- eval (extract v_9582 1 17);
      setRegister (lhs.of_reg v_3002) v_9589;
      setRegister of (mux (notBool_ (eq v_9584 v_9587)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9582 9 17));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9589);
      setRegister sf (mux v_9587 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_9584 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3002 : reg (bv 16)) => do
      v_9603 <- getRegister v_3002;
      v_9606 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_9603) 1) 0 17);
      v_9607 <- eval (extract v_9606 0 1);
      v_9608 <- eval (extract v_9606 1 2);
      v_9609 <- eval (extract v_9606 1 17);
      setRegister (lhs.of_reg v_3002) v_9609;
      setRegister of (mux (notBool_ (eq (eq v_9607 (expression.bv_nat 1 1)) (eq v_9608 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9606 9 17));
      setRegister af undef;
      setRegister zf (zeroFlag v_9609);
      setRegister sf v_9608;
      setRegister cf v_9607;
      pure ()
    pat_end;
    pattern fun cl (v_2980 : Mem) => do
      v_16116 <- evaluateAddress v_2980;
      v_16117 <- load v_16116 2;
      v_16119 <- getRegister rcx;
      v_16121 <- eval (bv_and (extract v_16119 56 64) (expression.bv_nat 8 31));
      v_16125 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_16117) (uvalueMInt (concat (expression.bv_nat 9 0) v_16121))) 0 17);
      v_16126 <- eval (extract v_16125 1 17);
      store v_16116 v_16126 2;
      v_16128 <- eval (uge v_16121 (expression.bv_nat 8 16));
      v_16131 <- eval (eq v_16121 (expression.bv_nat 8 0));
      v_16132 <- eval (notBool_ v_16131);
      v_16136 <- getRegister cf;
      v_16141 <- eval (bit_or (bit_and v_16128 undef) (bit_and (notBool_ v_16128) (bit_or (bit_and v_16132 (eq (extract v_16125 0 1) (expression.bv_nat 1 1))) (bit_and v_16131 (eq v_16136 (expression.bv_nat 1 1))))));
      v_16144 <- eval (eq (extract v_16125 1 2) (expression.bv_nat 1 1));
      v_16146 <- getRegister sf;
      v_16153 <- getRegister zf;
      v_16158 <- eval (bit_and v_16132 undef);
      v_16159 <- getRegister af;
      v_16194 <- getRegister pf;
      v_16199 <- eval (eq v_16121 (expression.bv_nat 8 1));
      v_16204 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16199 (notBool_ (eq v_16141 v_16144))) (bit_and (notBool_ v_16199) (bit_or v_16158 (bit_and v_16131 (eq v_16204 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16132 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16125 16 17) (expression.bv_nat 1 1)) (eq (extract v_16125 15 16) (expression.bv_nat 1 1)))) (eq (extract v_16125 14 15) (expression.bv_nat 1 1)))) (eq (extract v_16125 13 14) (expression.bv_nat 1 1)))) (eq (extract v_16125 12 13) (expression.bv_nat 1 1)))) (eq (extract v_16125 11 12) (expression.bv_nat 1 1)))) (eq (extract v_16125 10 11) (expression.bv_nat 1 1)))) (eq (extract v_16125 9 10) (expression.bv_nat 1 1)))) (bit_and v_16131 (eq v_16194 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16158 (bit_and v_16131 (eq v_16159 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16132 (eq v_16126 (expression.bv_nat 16 0))) (bit_and v_16131 (eq v_16153 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16132 v_16144) (bit_and v_16131 (eq v_16146 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_16141 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2984 : imm int) (v_2983 : Mem) => do
      v_16217 <- evaluateAddress v_2983;
      v_16218 <- load v_16217 2;
      v_16221 <- eval (bv_and (handleImmediateWithSignExtend v_2984 8 8) (expression.bv_nat 8 31));
      v_16225 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_16218) (uvalueMInt (concat (expression.bv_nat 9 0) v_16221))) 0 17);
      v_16226 <- eval (extract v_16225 1 17);
      store v_16217 v_16226 2;
      v_16228 <- eval (uge v_16221 (expression.bv_nat 8 16));
      v_16231 <- eval (eq v_16221 (expression.bv_nat 8 0));
      v_16232 <- eval (notBool_ v_16231);
      v_16236 <- getRegister cf;
      v_16241 <- eval (bit_or (bit_and v_16228 undef) (bit_and (notBool_ v_16228) (bit_or (bit_and v_16232 (eq (extract v_16225 0 1) (expression.bv_nat 1 1))) (bit_and v_16231 (eq v_16236 (expression.bv_nat 1 1))))));
      v_16244 <- eval (eq (extract v_16225 1 2) (expression.bv_nat 1 1));
      v_16246 <- getRegister sf;
      v_16253 <- getRegister zf;
      v_16258 <- eval (bit_and v_16232 undef);
      v_16259 <- getRegister af;
      v_16294 <- getRegister pf;
      v_16299 <- eval (eq v_16221 (expression.bv_nat 8 1));
      v_16304 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_16299 (notBool_ (eq v_16241 v_16244))) (bit_and (notBool_ v_16299) (bit_or v_16258 (bit_and v_16231 (eq v_16304 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16232 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16225 16 17) (expression.bv_nat 1 1)) (eq (extract v_16225 15 16) (expression.bv_nat 1 1)))) (eq (extract v_16225 14 15) (expression.bv_nat 1 1)))) (eq (extract v_16225 13 14) (expression.bv_nat 1 1)))) (eq (extract v_16225 12 13) (expression.bv_nat 1 1)))) (eq (extract v_16225 11 12) (expression.bv_nat 1 1)))) (eq (extract v_16225 10 11) (expression.bv_nat 1 1)))) (eq (extract v_16225 9 10) (expression.bv_nat 1 1)))) (bit_and v_16231 (eq v_16294 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16258 (bit_and v_16231 (eq v_16259 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16232 (eq v_16226 (expression.bv_nat 16 0))) (bit_and v_16231 (eq v_16253 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16232 v_16244) (bit_and v_16231 (eq v_16246 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_16241 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2987 : Mem) => do
      v_18063 <- evaluateAddress v_2987;
      v_18064 <- load v_18063 2;
      v_18067 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_18064) 1) 0 17);
      v_18068 <- eval (extract v_18067 1 17);
      store v_18063 v_18068 2;
      v_18071 <- eval (eq (extract v_18067 0 1) (expression.bv_nat 1 1));
      v_18074 <- eval (eq (extract v_18067 1 2) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq v_18071 v_18074)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18067 9 17));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18068);
      setRegister sf (mux v_18074 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_18071 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2987 : Mem) => do
      v_18088 <- evaluateAddress v_2987;
      v_18089 <- load v_18088 2;
      v_18092 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_18089) 1) 0 17);
      v_18093 <- eval (extract v_18092 1 17);
      store v_18088 v_18093 2;
      v_18095 <- eval (extract v_18092 0 1);
      v_18096 <- eval (extract v_18092 1 2);
      setRegister of (mux (notBool_ (eq (eq v_18095 (expression.bv_nat 1 1)) (eq v_18096 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18092 9 17));
      setRegister af undef;
      setRegister zf (zeroFlag v_18093);
      setRegister sf v_18096;
      setRegister cf v_18095;
      pure ()
    pat_end
