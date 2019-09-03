def psrld1 : instruction :=
  definst "psrld" $ do
    pattern fun (v_3044 : imm int) (v_3045 : reg (bv 128)) => do
      v_7860 <- eval (handleImmediateWithSignExtend v_3044 8 8);
      v_7863 <- getRegister v_3045;
      v_7866 <- eval (uvalueMInt (concat (expression.bv_nat 24 0) v_7860));
      setRegister (lhs.of_reg v_3045) (mux (ugt (concat (expression.bv_nat 56 0) v_7860) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_7863 0 32) v_7866) (concat (lshr (extract v_7863 32 64) v_7866) (concat (lshr (extract v_7863 64 96) v_7866) (lshr (extract v_7863 96 128) v_7866)))));
      pure ()
    pat_end;
    pattern fun (v_3053 : reg (bv 128)) (v_3054 : reg (bv 128)) => do
      v_7883 <- getRegister v_3053;
      v_7886 <- getRegister v_3054;
      v_7889 <- eval (uvalueMInt (extract v_7883 96 128));
      setRegister (lhs.of_reg v_3054) (mux (ugt (extract v_7883 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_7886 0 32) v_7889) (concat (lshr (extract v_7886 32 64) v_7889) (concat (lshr (extract v_7886 64 96) v_7889) (lshr (extract v_7886 96 128) v_7889)))));
      pure ()
    pat_end;
    pattern fun (v_3049 : Mem) (v_3050 : reg (bv 128)) => do
      v_14564 <- evaluateAddress v_3049;
      v_14565 <- load v_14564 16;
      v_14568 <- getRegister v_3050;
      v_14571 <- eval (uvalueMInt (extract v_14565 96 128));
      setRegister (lhs.of_reg v_3050) (mux (ugt (extract v_14565 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat (lshr (extract v_14568 0 32) v_14571) (concat (lshr (extract v_14568 32 64) v_14571) (concat (lshr (extract v_14568 64 96) v_14571) (lshr (extract v_14568 96 128) v_14571)))));
      pure ()
    pat_end
