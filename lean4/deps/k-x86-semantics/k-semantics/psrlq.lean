def psrlq1 : instruction :=
  definst "psrlq" $ do
    pattern fun (v_3140 : imm int) (v_3141 : reg (bv 128)) => do
      v_7880 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend v_3140 8 8));
      v_7882 <- getRegister v_3141;
      setRegister (lhs.of_reg v_3141) (mux (ugt v_7880 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_7882 0 64) v_7880) (lshr (extract v_7882 64 128) v_7880)));
      pure ()
    pat_end;
    pattern fun (v_3149 : reg (bv 128)) (v_3150 : reg (bv 128)) => do
      v_7894 <- getRegister v_3149;
      v_7895 <- eval (extract v_7894 64 128);
      v_7897 <- getRegister v_3150;
      setRegister (lhs.of_reg v_3150) (mux (ugt v_7895 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_7897 0 64) v_7895) (lshr (extract v_7897 64 128) v_7895)));
      pure ()
    pat_end;
    pattern fun (v_3145 : Mem) (v_3146 : reg (bv 128)) => do
      v_14360 <- evaluateAddress v_3145;
      v_14361 <- load v_14360 16;
      v_14362 <- eval (extract v_14361 64 128);
      v_14364 <- getRegister v_3146;
      setRegister (lhs.of_reg v_3146) (mux (ugt v_14362 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) (concat (lshr (extract v_14364 0 64) v_14362) (lshr (extract v_14364 64 128) v_14362)));
      pure ()
    pat_end
