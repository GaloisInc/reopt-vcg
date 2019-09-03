def sarl1 : instruction :=
  definst "sarl" $ do
    pattern fun cl (v_3056 : reg (bv 32)) => do
      v_7481 <- getRegister rcx;
      v_7483 <- eval (bv_and (extract v_7481 56 64) (expression.bv_nat 8 31));
      v_7484 <- eval (eq v_7483 (expression.bv_nat 8 0));
      v_7485 <- eval (notBool_ v_7484);
      v_7486 <- getRegister v_3056;
      v_7487 <- eval (concat v_7486 (expression.bv_nat 1 0));
      v_7493 <- eval (ashr (mi (bitwidthMInt v_7487) (svalueMInt v_7487)) (uvalueMInt (concat (expression.bv_nat 25 0) v_7483)));
      v_7497 <- getRegister cf;
      v_7505 <- getRegister sf;
      v_7510 <- eval (bit_and v_7485 undef);
      v_7511 <- getRegister af;
      v_7516 <- eval (extract v_7493 0 32);
      v_7519 <- getRegister zf;
      v_7554 <- getRegister pf;
      v_7561 <- getRegister of;
      setRegister (lhs.of_reg v_3056) v_7516;
      setRegister of (mux (bit_and (notBool_ (eq v_7483 (expression.bv_nat 8 1))) (bit_or v_7510 (bit_and v_7484 (eq v_7561 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7485 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7493 31 32) (expression.bv_nat 1 1)) (eq (extract v_7493 30 31) (expression.bv_nat 1 1)))) (eq (extract v_7493 29 30) (expression.bv_nat 1 1)))) (eq (extract v_7493 28 29) (expression.bv_nat 1 1)))) (eq (extract v_7493 27 28) (expression.bv_nat 1 1)))) (eq (extract v_7493 26 27) (expression.bv_nat 1 1)))) (eq (extract v_7493 25 26) (expression.bv_nat 1 1)))) (eq (extract v_7493 24 25) (expression.bv_nat 1 1)))) (bit_and v_7484 (eq v_7554 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7485 (eq v_7516 (expression.bv_nat 32 0))) (bit_and v_7484 (eq v_7519 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7510 (bit_and v_7484 (eq v_7511 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7485 (eq (extract v_7493 0 1) (expression.bv_nat 1 1))) (bit_and v_7484 (eq v_7505 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7485 (eq (extract v_7493 32 33) (expression.bv_nat 1 1))) (bit_and v_7484 (eq v_7497 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3058 : imm int) (v_3061 : reg (bv 32)) => do
      v_7575 <- eval (bv_and (handleImmediateWithSignExtend v_3058 8 8) (expression.bv_nat 8 31));
      v_7576 <- eval (eq v_7575 (expression.bv_nat 8 0));
      v_7577 <- eval (notBool_ v_7576);
      v_7578 <- getRegister v_3061;
      v_7579 <- eval (concat v_7578 (expression.bv_nat 1 0));
      v_7585 <- eval (ashr (mi (bitwidthMInt v_7579) (svalueMInt v_7579)) (uvalueMInt (concat (expression.bv_nat 25 0) v_7575)));
      v_7589 <- getRegister cf;
      v_7597 <- getRegister sf;
      v_7602 <- eval (bit_and v_7577 undef);
      v_7603 <- getRegister af;
      v_7608 <- eval (extract v_7585 0 32);
      v_7611 <- getRegister zf;
      v_7646 <- getRegister pf;
      v_7653 <- getRegister of;
      setRegister (lhs.of_reg v_3061) v_7608;
      setRegister of (mux (bit_and (notBool_ (eq v_7575 (expression.bv_nat 8 1))) (bit_or v_7602 (bit_and v_7576 (eq v_7653 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7577 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7585 31 32) (expression.bv_nat 1 1)) (eq (extract v_7585 30 31) (expression.bv_nat 1 1)))) (eq (extract v_7585 29 30) (expression.bv_nat 1 1)))) (eq (extract v_7585 28 29) (expression.bv_nat 1 1)))) (eq (extract v_7585 27 28) (expression.bv_nat 1 1)))) (eq (extract v_7585 26 27) (expression.bv_nat 1 1)))) (eq (extract v_7585 25 26) (expression.bv_nat 1 1)))) (eq (extract v_7585 24 25) (expression.bv_nat 1 1)))) (bit_and v_7576 (eq v_7646 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7577 (eq v_7608 (expression.bv_nat 32 0))) (bit_and v_7576 (eq v_7611 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7602 (bit_and v_7576 (eq v_7603 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7577 (eq (extract v_7585 0 1) (expression.bv_nat 1 1))) (bit_and v_7576 (eq v_7597 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7577 (eq (extract v_7585 32 33) (expression.bv_nat 1 1))) (bit_and v_7576 (eq v_7589 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_3068 : reg (bv 32)) => do
      v_7668 <- getRegister v_3068;
      v_7669 <- eval (concat v_7668 (expression.bv_nat 1 0));
      v_7673 <- eval (ashr (mi (bitwidthMInt v_7669) (svalueMInt v_7669)) 1);
      v_7676 <- eval (extract v_7673 0 32);
      setRegister (lhs.of_reg v_3068) v_7676;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_7673 24 32));
      setRegister zf (zeroFlag v_7676);
      setRegister af undef;
      setRegister sf (extract v_7673 0 1);
      setRegister cf (extract v_7673 32 33);
      pure ()
    pat_end;
    pattern fun (v_3065 : reg (bv 32)) => do
      v_9855 <- getRegister v_3065;
      v_9856 <- eval (concat v_9855 (expression.bv_nat 1 0));
      v_9860 <- eval (ashr (mi (bitwidthMInt v_9856) (svalueMInt v_9856)) 1);
      v_9867 <- eval (extract v_9860 0 32);
      setRegister (lhs.of_reg v_3065) v_9867;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9860 24 32));
      setRegister zf (zeroFlag v_9867);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_9860 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_9860 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3065 : reg (bv 32)) => do
      v_9878 <- getRegister v_3065;
      v_9879 <- eval (concat v_9878 (expression.bv_nat 1 0));
      v_9883 <- eval (ashr (mi (bitwidthMInt v_9879) (svalueMInt v_9879)) 1);
      v_9886 <- eval (extract v_9883 0 32);
      setRegister (lhs.of_reg v_3065) v_9886;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9883 24 32));
      setRegister zf (zeroFlag v_9886);
      setRegister af undef;
      setRegister sf (extract v_9883 0 1);
      setRegister cf (extract v_9883 32 33);
      pure ()
    pat_end;
    pattern fun cl (v_3041 : Mem) => do
      v_16892 <- evaluateAddress v_3041;
      v_16893 <- load v_16892 4;
      v_16894 <- eval (concat v_16893 (expression.bv_nat 1 0));
      v_16898 <- getRegister rcx;
      v_16900 <- eval (bv_and (extract v_16898 56 64) (expression.bv_nat 8 31));
      v_16903 <- eval (ashr (mi (bitwidthMInt v_16894) (svalueMInt v_16894)) (uvalueMInt (concat (expression.bv_nat 25 0) v_16900)));
      v_16904 <- eval (extract v_16903 0 32);
      store v_16892 v_16904 4;
      v_16906 <- eval (eq v_16900 (expression.bv_nat 8 0));
      v_16907 <- eval (notBool_ v_16906);
      v_16911 <- getRegister cf;
      v_16919 <- getRegister sf;
      v_16926 <- getRegister zf;
      v_16931 <- eval (bit_and v_16907 undef);
      v_16932 <- getRegister af;
      v_16967 <- getRegister pf;
      v_16974 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_16900 (expression.bv_nat 8 1))) (bit_or v_16931 (bit_and v_16906 (eq v_16974 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16907 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16903 31 32) (expression.bv_nat 1 1)) (eq (extract v_16903 30 31) (expression.bv_nat 1 1)))) (eq (extract v_16903 29 30) (expression.bv_nat 1 1)))) (eq (extract v_16903 28 29) (expression.bv_nat 1 1)))) (eq (extract v_16903 27 28) (expression.bv_nat 1 1)))) (eq (extract v_16903 26 27) (expression.bv_nat 1 1)))) (eq (extract v_16903 25 26) (expression.bv_nat 1 1)))) (eq (extract v_16903 24 25) (expression.bv_nat 1 1)))) (bit_and v_16906 (eq v_16967 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16931 (bit_and v_16906 (eq v_16932 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16907 (eq v_16904 (expression.bv_nat 32 0))) (bit_and v_16906 (eq v_16926 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16907 (eq (extract v_16903 0 1) (expression.bv_nat 1 1))) (bit_and v_16906 (eq v_16919 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_16907 (eq (extract v_16903 32 33) (expression.bv_nat 1 1))) (bit_and v_16906 (eq v_16911 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3044 : imm int) (v_3045 : Mem) => do
      v_16986 <- evaluateAddress v_3045;
      v_16987 <- load v_16986 4;
      v_16988 <- eval (concat v_16987 (expression.bv_nat 1 0));
      v_16993 <- eval (bv_and (handleImmediateWithSignExtend v_3044 8 8) (expression.bv_nat 8 31));
      v_16996 <- eval (ashr (mi (bitwidthMInt v_16988) (svalueMInt v_16988)) (uvalueMInt (concat (expression.bv_nat 25 0) v_16993)));
      v_16997 <- eval (extract v_16996 0 32);
      store v_16986 v_16997 4;
      v_16999 <- eval (eq v_16993 (expression.bv_nat 8 0));
      v_17000 <- eval (notBool_ v_16999);
      v_17004 <- getRegister cf;
      v_17012 <- getRegister sf;
      v_17019 <- getRegister zf;
      v_17024 <- eval (bit_and v_17000 undef);
      v_17025 <- getRegister af;
      v_17060 <- getRegister pf;
      v_17067 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_16993 (expression.bv_nat 8 1))) (bit_or v_17024 (bit_and v_16999 (eq v_17067 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_17000 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16996 31 32) (expression.bv_nat 1 1)) (eq (extract v_16996 30 31) (expression.bv_nat 1 1)))) (eq (extract v_16996 29 30) (expression.bv_nat 1 1)))) (eq (extract v_16996 28 29) (expression.bv_nat 1 1)))) (eq (extract v_16996 27 28) (expression.bv_nat 1 1)))) (eq (extract v_16996 26 27) (expression.bv_nat 1 1)))) (eq (extract v_16996 25 26) (expression.bv_nat 1 1)))) (eq (extract v_16996 24 25) (expression.bv_nat 1 1)))) (bit_and v_16999 (eq v_17060 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_17024 (bit_and v_16999 (eq v_17025 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_17000 (eq v_16997 (expression.bv_nat 32 0))) (bit_and v_16999 (eq v_17019 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_17000 (eq (extract v_16996 0 1) (expression.bv_nat 1 1))) (bit_and v_16999 (eq v_17012 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_17000 (eq (extract v_16996 32 33) (expression.bv_nat 1 1))) (bit_and v_16999 (eq v_17004 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3050 : Mem) => do
      v_18438 <- evaluateAddress v_3050;
      v_18439 <- load v_18438 4;
      v_18440 <- eval (concat v_18439 (expression.bv_nat 1 0));
      v_18444 <- eval (ashr (mi (bitwidthMInt v_18440) (svalueMInt v_18440)) 1);
      v_18445 <- eval (extract v_18444 0 32);
      store v_18438 v_18445 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18444 24 32));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18445);
      setRegister sf (mux (eq (extract v_18444 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_18444 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3050 : Mem) => do
      v_18462 <- evaluateAddress v_3050;
      v_18463 <- load v_18462 4;
      v_18464 <- eval (concat v_18463 (expression.bv_nat 1 0));
      v_18468 <- eval (ashr (mi (bitwidthMInt v_18464) (svalueMInt v_18464)) 1);
      v_18469 <- eval (extract v_18468 0 32);
      store v_18462 v_18469 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18468 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_18469);
      setRegister sf (extract v_18468 0 1);
      setRegister cf (extract v_18468 32 33);
      pure ()
    pat_end
