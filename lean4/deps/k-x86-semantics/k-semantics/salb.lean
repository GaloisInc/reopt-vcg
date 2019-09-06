def salb1 : instruction :=
  definst "salb" $ do
    pattern fun (_ : clReg) (v_2987 : reg (bv 8)) => do
      v_5415 <- getRegister rcx;
      v_5417 <- eval (bv_and (extract v_5415 56 64) (expression.bv_nat 8 31));
      v_5418 <- eval (eq v_5417 (expression.bv_nat 8 0));
      v_5419 <- getRegister zf;
      v_5420 <- getRegister v_2987;
      v_5424 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5420) (concat (expression.bv_nat 1 0) v_5417)) 0 9);
      v_5425 <- eval (extract v_5424 1 9);
      v_5428 <- getRegister sf;
      v_5429 <- eval (isBitSet v_5424 1);
      v_5431 <- getRegister pf;
      v_5436 <- getRegister cf;
      v_5439 <- eval (mux (uge v_5417 (expression.bv_nat 8 8)) undef (mux v_5418 v_5436 (isBitSet v_5424 0)));
      v_5442 <- getRegister of;
      v_5445 <- getRegister af;
      setRegister (lhs.of_reg v_2987) v_5425;
      setRegister af (mux v_5418 v_5445 undef);
      setRegister cf v_5439;
      setRegister of (mux (eq v_5417 (expression.bv_nat 8 1)) (notBool_ (eq v_5439 v_5429)) (mux v_5418 v_5442 undef));
      setRegister pf (mux v_5418 v_5431 (parityFlag v_5425));
      setRegister sf (mux v_5418 v_5428 v_5429);
      setRegister zf (mux v_5418 v_5419 (eq v_5425 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2988 : imm int) (v_2992 : reg (bv 8)) => do
      v_5455 <- eval (bv_and (handleImmediateWithSignExtend v_2988 8 8) (expression.bv_nat 8 31));
      v_5456 <- eval (eq v_5455 (expression.bv_nat 8 0));
      v_5457 <- getRegister zf;
      v_5458 <- getRegister v_2992;
      v_5462 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_5458) (concat (expression.bv_nat 1 0) v_5455)) 0 9);
      v_5463 <- eval (extract v_5462 1 9);
      v_5466 <- getRegister sf;
      v_5467 <- eval (isBitSet v_5462 1);
      v_5469 <- getRegister pf;
      v_5474 <- getRegister cf;
      v_5477 <- eval (mux (uge v_5455 (expression.bv_nat 8 8)) undef (mux v_5456 v_5474 (isBitSet v_5462 0)));
      v_5480 <- getRegister of;
      v_5483 <- getRegister af;
      setRegister (lhs.of_reg v_2992) v_5463;
      setRegister af (mux v_5456 v_5483 undef);
      setRegister cf v_5477;
      setRegister of (mux (eq v_5455 (expression.bv_nat 8 1)) (notBool_ (eq v_5477 v_5467)) (mux v_5456 v_5480 undef));
      setRegister pf (mux v_5456 v_5469 (parityFlag v_5463));
      setRegister sf (mux v_5456 v_5466 v_5467);
      setRegister zf (mux v_5456 v_5457 (eq v_5463 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2995 : reg (bv 8)) => do
      v_7474 <- getRegister v_2995;
      v_7477 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_7474) (expression.bv_nat 9 1)) 0 9);
      v_7478 <- eval (extract v_7477 1 9);
      v_7480 <- eval (isBitSet v_7477 1);
      v_7482 <- eval (isBitSet v_7477 0);
      setRegister (lhs.of_reg v_2995) v_7478;
      setRegister af undef;
      setRegister cf v_7482;
      setRegister of (notBool_ (eq v_7482 v_7480));
      setRegister pf (parityFlag v_7478);
      setRegister sf v_7480;
      setRegister zf (zeroFlag v_7478);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2955 : Mem) => do
      v_11857 <- evaluateAddress v_2955;
      v_11858 <- load v_11857 1;
      v_11860 <- getRegister rcx;
      v_11862 <- eval (bv_and (extract v_11860 56 64) (expression.bv_nat 8 31));
      v_11865 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_11858) (concat (expression.bv_nat 1 0) v_11862)) 0 9);
      v_11866 <- eval (extract v_11865 1 9);
      store v_11857 v_11866 1;
      v_11868 <- eval (eq v_11862 (expression.bv_nat 8 0));
      v_11869 <- getRegister zf;
      v_11872 <- getRegister sf;
      v_11873 <- eval (isBitSet v_11865 1);
      v_11875 <- getRegister pf;
      v_11880 <- getRegister cf;
      v_11883 <- eval (mux (uge v_11862 (expression.bv_nat 8 8)) undef (mux v_11868 v_11880 (isBitSet v_11865 0)));
      v_11886 <- getRegister of;
      v_11889 <- getRegister af;
      setRegister af (mux v_11868 v_11889 undef);
      setRegister cf v_11883;
      setRegister of (mux (eq v_11862 (expression.bv_nat 8 1)) (notBool_ (eq v_11883 v_11873)) (mux v_11868 v_11886 undef));
      setRegister pf (mux v_11868 v_11875 (parityFlag v_11866));
      setRegister sf (mux v_11868 v_11872 v_11873);
      setRegister zf (mux v_11868 v_11869 (eq v_11866 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2958 : imm int) (v_2959 : Mem) => do
      v_11897 <- evaluateAddress v_2959;
      v_11898 <- load v_11897 1;
      v_11901 <- eval (bv_and (handleImmediateWithSignExtend v_2958 8 8) (expression.bv_nat 8 31));
      v_11904 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_11898) (concat (expression.bv_nat 1 0) v_11901)) 0 9);
      v_11905 <- eval (extract v_11904 1 9);
      store v_11897 v_11905 1;
      v_11907 <- eval (eq v_11901 (expression.bv_nat 8 0));
      v_11908 <- getRegister zf;
      v_11911 <- getRegister sf;
      v_11912 <- eval (isBitSet v_11904 1);
      v_11914 <- getRegister pf;
      v_11919 <- getRegister cf;
      v_11922 <- eval (mux (uge v_11901 (expression.bv_nat 8 8)) undef (mux v_11907 v_11919 (isBitSet v_11904 0)));
      v_11925 <- getRegister of;
      v_11928 <- getRegister af;
      setRegister af (mux v_11907 v_11928 undef);
      setRegister cf v_11922;
      setRegister of (mux (eq v_11901 (expression.bv_nat 8 1)) (notBool_ (eq v_11922 v_11912)) (mux v_11907 v_11925 undef));
      setRegister pf (mux v_11907 v_11914 (parityFlag v_11905));
      setRegister sf (mux v_11907 v_11911 v_11912);
      setRegister zf (mux v_11907 v_11908 (eq v_11905 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2964 : Mem) => do
      v_13115 <- evaluateAddress v_2964;
      v_13116 <- load v_13115 1;
      v_13119 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_13116) (expression.bv_nat 9 1)) 0 9);
      v_13120 <- eval (extract v_13119 1 9);
      store v_13115 v_13120 1;
      v_13123 <- eval (isBitSet v_13119 1);
      v_13125 <- eval (isBitSet v_13119 0);
      setRegister af undef;
      setRegister cf v_13125;
      setRegister of (notBool_ (eq v_13125 v_13123));
      setRegister pf (parityFlag v_13120);
      setRegister sf v_13123;
      setRegister zf (zeroFlag v_13120);
      pure ()
    pat_end
