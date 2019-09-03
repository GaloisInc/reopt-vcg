def psllq1 : instruction :=
  definst "psllq" $ do
    pattern fun (v_2975 : imm int) (v_2974 : reg (bv 128)) => do
      v_7817 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_2975 8 8));
      v_7819 <- getRegister v_2974;
      v_7820 <- eval (extract v_7819 0 64);
      v_7821 <- eval (uvalueMInt v_7817);
      v_7825 <- eval (extract v_7819 64 128);
      setRegister (lhs.of_reg v_2974) (mux (ugt v_7817 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl v_7820 v_7821) 0 (bitwidthMInt v_7820)) (extract (shl v_7825 v_7821) 0 (bitwidthMInt v_7825))));
      pure ()
    pat_end;
    pattern fun (v_2983 : reg (bv 128)) (v_2984 : reg (bv 128)) => do
      v_7836 <- getRegister v_2983;
      v_7837 <- eval (extract v_7836 64 128);
      v_7839 <- getRegister v_2984;
      v_7840 <- eval (extract v_7839 0 64);
      v_7841 <- eval (uvalueMInt v_7837);
      v_7845 <- eval (extract v_7839 64 128);
      setRegister (lhs.of_reg v_2984) (mux (ugt v_7837 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl v_7840 v_7841) 0 (bitwidthMInt v_7840)) (extract (shl v_7845 v_7841) 0 (bitwidthMInt v_7845))));
      pure ()
    pat_end;
    pattern fun (v_2978 : Mem) (v_2979 : reg (bv 128)) => do
      v_14980 <- evaluateAddress v_2978;
      v_14981 <- load v_14980 16;
      v_14982 <- eval (extract v_14981 64 128);
      v_14984 <- getRegister v_2979;
      v_14985 <- eval (extract v_14984 0 64);
      v_14986 <- eval (uvalueMInt v_14982);
      v_14990 <- eval (extract v_14984 64 128);
      setRegister (lhs.of_reg v_2979) (mux (ugt v_14982 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (extract (shl v_14985 v_14986) 0 (bitwidthMInt v_14985)) (extract (shl v_14990 v_14986) 0 (bitwidthMInt v_14990))));
      pure ()
    pat_end
