def psrld1 : instruction :=
  definst "psrld" $ do
    pattern fun (v_3094 : imm int) (v_3093 : reg (bv 128)) => do
      v_7803 <- eval (handleImmediateWithSignExtend v_3094 8 8);
      v_7806 <- getRegister v_3093;
      v_7808 <- eval (concat (expression.bv_nat 24 0) v_7803);
      setRegister (lhs.of_reg v_3093) (mux (ugt (concat (expression.bv_nat 56 0) v_7803) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_7806 0 32) v_7808) (concat (lshr (extract v_7806 32 64) v_7808) (concat (lshr (extract v_7806 64 96) v_7808) (lshr (extract v_7806 96 128) v_7808)))));
      pure ()
    pat_end;
    pattern fun (v_3102 : reg (bv 128)) (v_3103 : reg (bv 128)) => do
      v_7825 <- getRegister v_3102;
      v_7828 <- getRegister v_3103;
      v_7830 <- eval (extract v_7825 96 128);
      setRegister (lhs.of_reg v_3103) (mux (ugt (extract v_7825 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_7828 0 32) v_7830) (concat (lshr (extract v_7828 32 64) v_7830) (concat (lshr (extract v_7828 64 96) v_7830) (lshr (extract v_7828 96 128) v_7830)))));
      pure ()
    pat_end;
    pattern fun (v_3099 : Mem) (v_3098 : reg (bv 128)) => do
      v_14365 <- evaluateAddress v_3099;
      v_14366 <- load v_14365 16;
      v_14369 <- getRegister v_3098;
      v_14371 <- eval (extract v_14366 96 128);
      setRegister (lhs.of_reg v_3098) (mux (ugt (extract v_14366 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_14369 0 32) v_14371) (concat (lshr (extract v_14369 32 64) v_14371) (concat (lshr (extract v_14369 64 96) v_14371) (lshr (extract v_14369 96 128) v_14371)))));
      pure ()
    pat_end
