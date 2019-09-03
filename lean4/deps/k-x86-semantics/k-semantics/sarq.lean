def sarq1 : instruction :=
  definst "sarq" $ do
    pattern fun cl (v_3097 : reg (bv 64)) => do
      v_7699 <- getRegister rcx;
      v_7701 <- eval (bv_and (extract v_7699 56 64) (expression.bv_nat 8 63));
      v_7702 <- eval (eq v_7701 (expression.bv_nat 8 0));
      v_7703 <- eval (notBool_ v_7702);
      v_7704 <- getRegister v_3097;
      v_7710 <- eval (ashr (mi 65 (svalueMInt (concat v_7704 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 57 0) v_7701)));
      v_7714 <- getRegister cf;
      v_7722 <- getRegister sf;
      v_7727 <- eval (extract v_7710 0 64);
      v_7730 <- getRegister zf;
      v_7735 <- eval (bit_and v_7703 undef);
      v_7736 <- getRegister af;
      v_7771 <- getRegister pf;
      v_7778 <- getRegister of;
      setRegister (lhs.of_reg v_3097) v_7727;
      setRegister of (mux (bit_and (notBool_ (eq v_7701 (expression.bv_nat 8 1))) (bit_or v_7735 (bit_and v_7702 (eq v_7778 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7703 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7710 63 64) (expression.bv_nat 1 1)) (eq (extract v_7710 62 63) (expression.bv_nat 1 1)))) (eq (extract v_7710 61 62) (expression.bv_nat 1 1)))) (eq (extract v_7710 60 61) (expression.bv_nat 1 1)))) (eq (extract v_7710 59 60) (expression.bv_nat 1 1)))) (eq (extract v_7710 58 59) (expression.bv_nat 1 1)))) (eq (extract v_7710 57 58) (expression.bv_nat 1 1)))) (eq (extract v_7710 56 57) (expression.bv_nat 1 1)))) (bit_and v_7702 (eq v_7771 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7735 (bit_and v_7702 (eq v_7736 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7703 (eq v_7727 (expression.bv_nat 64 0))) (bit_and v_7702 (eq v_7730 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7703 (eq (extract v_7710 0 1) (expression.bv_nat 1 1))) (bit_and v_7702 (eq v_7722 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7703 (eq (extract v_7710 64 65) (expression.bv_nat 1 1))) (bit_and v_7702 (eq v_7714 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3100 : imm int) (v_3102 : reg (bv 64)) => do
      v_7792 <- eval (bv_and (handleImmediateWithSignExtend v_3100 8 8) (expression.bv_nat 8 63));
      v_7793 <- eval (eq v_7792 (expression.bv_nat 8 0));
      v_7794 <- eval (notBool_ v_7793);
      v_7795 <- getRegister v_3102;
      v_7801 <- eval (ashr (mi 65 (svalueMInt (concat v_7795 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 57 0) v_7792)));
      v_7805 <- getRegister cf;
      v_7813 <- getRegister sf;
      v_7818 <- eval (extract v_7801 0 64);
      v_7821 <- getRegister zf;
      v_7826 <- eval (bit_and v_7794 undef);
      v_7827 <- getRegister af;
      v_7862 <- getRegister pf;
      v_7869 <- getRegister of;
      setRegister (lhs.of_reg v_3102) v_7818;
      setRegister of (mux (bit_and (notBool_ (eq v_7792 (expression.bv_nat 8 1))) (bit_or v_7826 (bit_and v_7793 (eq v_7869 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7794 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7801 63 64) (expression.bv_nat 1 1)) (eq (extract v_7801 62 63) (expression.bv_nat 1 1)))) (eq (extract v_7801 61 62) (expression.bv_nat 1 1)))) (eq (extract v_7801 60 61) (expression.bv_nat 1 1)))) (eq (extract v_7801 59 60) (expression.bv_nat 1 1)))) (eq (extract v_7801 58 59) (expression.bv_nat 1 1)))) (eq (extract v_7801 57 58) (expression.bv_nat 1 1)))) (eq (extract v_7801 56 57) (expression.bv_nat 1 1)))) (bit_and v_7793 (eq v_7862 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7826 (bit_and v_7793 (eq v_7827 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7794 (eq v_7818 (expression.bv_nat 64 0))) (bit_and v_7793 (eq v_7821 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7794 (eq (extract v_7801 0 1) (expression.bv_nat 1 1))) (bit_and v_7793 (eq v_7813 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7794 (eq (extract v_7801 64 65) (expression.bv_nat 1 1))) (bit_and v_7793 (eq v_7805 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_3109 : reg (bv 64)) => do
      v_7884 <- getRegister v_3109;
      v_7888 <- eval (ashr (mi 65 (svalueMInt (concat v_7884 (expression.bv_nat 1 0)))) 1);
      v_7891 <- eval (extract v_7888 0 64);
      setRegister (lhs.of_reg v_3109) v_7891;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_7888 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_7891);
      setRegister sf (extract v_7888 0 1);
      setRegister cf (extract v_7888 64 65);
      pure ()
    pat_end;
    pattern fun (v_3105 : reg (bv 64)) => do
      v_9828 <- getRegister v_3105;
      v_9832 <- eval (ashr (mi 65 (svalueMInt (concat v_9828 (expression.bv_nat 1 0)))) 1);
      v_9839 <- eval (extract v_9832 0 64);
      setRegister (lhs.of_reg v_3105) v_9839;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9832 56 64));
      setRegister zf (zeroFlag v_9839);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_9832 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_9832 64 65) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3105 : reg (bv 64)) => do
      v_9850 <- getRegister v_3105;
      v_9854 <- eval (ashr (mi 65 (svalueMInt (concat v_9850 (expression.bv_nat 1 0)))) 1);
      v_9857 <- eval (extract v_9854 0 64);
      setRegister (lhs.of_reg v_3105) v_9857;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9854 56 64));
      setRegister zf (zeroFlag v_9857);
      setRegister af undef;
      setRegister sf (extract v_9854 0 1);
      setRegister cf (extract v_9854 64 65);
      pure ()
    pat_end;
    pattern fun cl (v_3083 : Mem) => do
      v_16949 <- evaluateAddress v_3083;
      v_16950 <- load v_16949 8;
      v_16954 <- getRegister rcx;
      v_16956 <- eval (bv_and (extract v_16954 56 64) (expression.bv_nat 8 63));
      v_16959 <- eval (ashr (mi 65 (svalueMInt (concat v_16950 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 57 0) v_16956)));
      v_16960 <- eval (extract v_16959 0 64);
      store v_16949 v_16960 8;
      v_16962 <- eval (eq v_16956 (expression.bv_nat 8 0));
      v_16963 <- eval (notBool_ v_16962);
      v_16967 <- getRegister cf;
      v_16975 <- getRegister sf;
      v_16982 <- getRegister zf;
      v_16987 <- eval (bit_and v_16963 undef);
      v_16988 <- getRegister af;
      v_17023 <- getRegister pf;
      v_17030 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_16956 (expression.bv_nat 8 1))) (bit_or v_16987 (bit_and v_16962 (eq v_17030 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16963 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16959 63 64) (expression.bv_nat 1 1)) (eq (extract v_16959 62 63) (expression.bv_nat 1 1)))) (eq (extract v_16959 61 62) (expression.bv_nat 1 1)))) (eq (extract v_16959 60 61) (expression.bv_nat 1 1)))) (eq (extract v_16959 59 60) (expression.bv_nat 1 1)))) (eq (extract v_16959 58 59) (expression.bv_nat 1 1)))) (eq (extract v_16959 57 58) (expression.bv_nat 1 1)))) (eq (extract v_16959 56 57) (expression.bv_nat 1 1)))) (bit_and v_16962 (eq v_17023 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16987 (bit_and v_16962 (eq v_16988 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16963 (eq v_16960 (expression.bv_nat 64 0))) (bit_and v_16962 (eq v_16982 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16963 (eq (extract v_16959 0 1) (expression.bv_nat 1 1))) (bit_and v_16962 (eq v_16975 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_16963 (eq (extract v_16959 64 65) (expression.bv_nat 1 1))) (bit_and v_16962 (eq v_16967 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3087 : imm int) (v_3086 : Mem) => do
      v_17042 <- evaluateAddress v_3086;
      v_17043 <- load v_17042 8;
      v_17048 <- eval (bv_and (handleImmediateWithSignExtend v_3087 8 8) (expression.bv_nat 8 63));
      v_17051 <- eval (ashr (mi 65 (svalueMInt (concat v_17043 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 57 0) v_17048)));
      v_17052 <- eval (extract v_17051 0 64);
      store v_17042 v_17052 8;
      v_17054 <- eval (eq v_17048 (expression.bv_nat 8 0));
      v_17055 <- eval (notBool_ v_17054);
      v_17059 <- getRegister cf;
      v_17067 <- getRegister sf;
      v_17074 <- getRegister zf;
      v_17079 <- eval (bit_and v_17055 undef);
      v_17080 <- getRegister af;
      v_17115 <- getRegister pf;
      v_17122 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_17048 (expression.bv_nat 8 1))) (bit_or v_17079 (bit_and v_17054 (eq v_17122 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_17055 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_17051 63 64) (expression.bv_nat 1 1)) (eq (extract v_17051 62 63) (expression.bv_nat 1 1)))) (eq (extract v_17051 61 62) (expression.bv_nat 1 1)))) (eq (extract v_17051 60 61) (expression.bv_nat 1 1)))) (eq (extract v_17051 59 60) (expression.bv_nat 1 1)))) (eq (extract v_17051 58 59) (expression.bv_nat 1 1)))) (eq (extract v_17051 57 58) (expression.bv_nat 1 1)))) (eq (extract v_17051 56 57) (expression.bv_nat 1 1)))) (bit_and v_17054 (eq v_17115 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_17079 (bit_and v_17054 (eq v_17080 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_17055 (eq v_17052 (expression.bv_nat 64 0))) (bit_and v_17054 (eq v_17074 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_17055 (eq (extract v_17051 0 1) (expression.bv_nat 1 1))) (bit_and v_17054 (eq v_17067 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_17055 (eq (extract v_17051 64 65) (expression.bv_nat 1 1))) (bit_and v_17054 (eq v_17059 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3090 : Mem) => do
      v_18193 <- evaluateAddress v_3090;
      v_18194 <- load v_18193 8;
      v_18198 <- eval (ashr (mi 65 (svalueMInt (concat v_18194 (expression.bv_nat 1 0)))) 1);
      v_18199 <- eval (extract v_18198 0 64);
      store v_18193 v_18199 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18198 56 64));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18199);
      setRegister sf (mux (eq (extract v_18198 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_18198 64 65) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3090 : Mem) => do
      v_18216 <- evaluateAddress v_3090;
      v_18217 <- load v_18216 8;
      v_18221 <- eval (ashr (mi 65 (svalueMInt (concat v_18217 (expression.bv_nat 1 0)))) 1);
      v_18222 <- eval (extract v_18221 0 64);
      store v_18216 v_18222 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18221 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_18222);
      setRegister sf (extract v_18221 0 1);
      setRegister cf (extract v_18221 64 65);
      pure ()
    pat_end
