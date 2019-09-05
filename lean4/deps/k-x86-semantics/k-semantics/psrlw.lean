def psrlw1 : instruction :=
  definst "psrlw" $ do
    pattern fun (v_3127 : imm int) (v_3126 : reg (bv 128)) => do
      v_7878 <- eval (handleImmediateWithSignExtend v_3127 8 8);
      v_7881 <- getRegister v_3126;
      v_7883 <- eval (concat (expression.bv_nat 8 0) v_7878);
      setRegister (lhs.of_reg v_3126) (mux (ugt (concat (expression.bv_nat 56 0) v_7878) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_7881 0 16) v_7883) (concat (lshr (extract v_7881 16 32) v_7883) (concat (lshr (extract v_7881 32 48) v_7883) (concat (lshr (extract v_7881 48 64) v_7883) (concat (lshr (extract v_7881 64 80) v_7883) (concat (lshr (extract v_7881 80 96) v_7883) (concat (lshr (extract v_7881 96 112) v_7883) (lshr (extract v_7881 112 128) v_7883)))))))));
      pure ()
    pat_end;
    pattern fun (v_3135 : reg (bv 128)) (v_3136 : reg (bv 128)) => do
      v_7912 <- getRegister v_3135;
      v_7915 <- getRegister v_3136;
      v_7917 <- eval (extract v_7912 112 128);
      setRegister (lhs.of_reg v_3136) (mux (ugt (extract v_7912 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_7915 0 16) v_7917) (concat (lshr (extract v_7915 16 32) v_7917) (concat (lshr (extract v_7915 32 48) v_7917) (concat (lshr (extract v_7915 48 64) v_7917) (concat (lshr (extract v_7915 64 80) v_7917) (concat (lshr (extract v_7915 80 96) v_7917) (concat (lshr (extract v_7915 96 112) v_7917) (lshr (extract v_7915 112 128) v_7917)))))))));
      pure ()
    pat_end;
    pattern fun (v_3132 : Mem) (v_3131 : reg (bv 128)) => do
      v_14396 <- evaluateAddress v_3132;
      v_14397 <- load v_14396 16;
      v_14400 <- getRegister v_3131;
      v_14402 <- eval (extract v_14397 112 128);
      setRegister (lhs.of_reg v_3131) (mux (ugt (extract v_14397 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_14400 0 16) v_14402) (concat (lshr (extract v_14400 16 32) v_14402) (concat (lshr (extract v_14400 32 48) v_14402) (concat (lshr (extract v_14400 48 64) v_14402) (concat (lshr (extract v_14400 64 80) v_14402) (concat (lshr (extract v_14400 80 96) v_14402) (concat (lshr (extract v_14400 96 112) v_14402) (lshr (extract v_14400 112 128) v_14402)))))))));
      pure ()
    pat_end
