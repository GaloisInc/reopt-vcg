def vperm2i1281 : instruction :=
  definst "vperm2i128" $ do
    pattern fun (v_3013 : imm int) (v_3014 : reg (bv 256)) (v_3015 : reg (bv 256)) (v_3016 : reg (bv 256)) => do
      v_8069 <- eval (handleImmediateWithSignExtend v_3013 8 8);
      v_8071 <- eval (extract v_8069 2 4);
      v_8073 <- getRegister v_3015;
      v_8074 <- eval (extract v_8073 128 256);
      v_8076 <- eval (extract v_8073 0 128);
      v_8078 <- getRegister v_3014;
      v_8079 <- eval (extract v_8078 128 256);
      v_8080 <- eval (extract v_8078 0 128);
      v_8086 <- eval (extract v_8069 6 8);
      setRegister (lhs.of_reg v_3016) (concat (mux (isBitSet v_8069 0) (expression.bv_nat 128 0) (mux (eq v_8071 (expression.bv_nat 2 0)) v_8074 (mux (eq v_8071 (expression.bv_nat 2 1)) v_8076 (mux (eq v_8071 (expression.bv_nat 2 2)) v_8079 v_8080)))) (mux (isBitSet v_8069 4) (expression.bv_nat 128 0) (mux (eq v_8086 (expression.bv_nat 2 0)) v_8074 (mux (eq v_8086 (expression.bv_nat 2 1)) v_8076 (mux (eq v_8086 (expression.bv_nat 2 2)) v_8079 v_8080)))));
      pure ()
    pat_end;
    pattern fun (v_3007 : imm int) (v_3008 : Mem) (v_3009 : reg (bv 256)) (v_3010 : reg (bv 256)) => do
      v_16615 <- eval (handleImmediateWithSignExtend v_3007 8 8);
      v_16617 <- eval (extract v_16615 2 4);
      v_16619 <- getRegister v_3009;
      v_16620 <- eval (extract v_16619 128 256);
      v_16622 <- eval (extract v_16619 0 128);
      v_16624 <- evaluateAddress v_3008;
      v_16625 <- load v_16624 32;
      v_16626 <- eval (extract v_16625 128 256);
      v_16627 <- eval (extract v_16625 0 128);
      v_16633 <- eval (extract v_16615 6 8);
      setRegister (lhs.of_reg v_3010) (concat (mux (isBitSet v_16615 0) (expression.bv_nat 128 0) (mux (eq v_16617 (expression.bv_nat 2 0)) v_16620 (mux (eq v_16617 (expression.bv_nat 2 1)) v_16622 (mux (eq v_16617 (expression.bv_nat 2 2)) v_16626 v_16627)))) (mux (isBitSet v_16615 4) (expression.bv_nat 128 0) (mux (eq v_16633 (expression.bv_nat 2 0)) v_16620 (mux (eq v_16633 (expression.bv_nat 2 1)) v_16622 (mux (eq v_16633 (expression.bv_nat 2 2)) v_16626 v_16627)))));
      pure ()
    pat_end
