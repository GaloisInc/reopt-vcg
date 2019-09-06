def vperm2f1281 : instruction :=
  definst "vperm2f128" $ do
    pattern fun (v_3027 : imm int) (v_3028 : reg (bv 256)) (v_3029 : reg (bv 256)) (v_3030 : reg (bv 256)) => do
      v_8063 <- eval (handleImmediateWithSignExtend v_3027 8 8);
      v_8065 <- eval (extract v_8063 2 4);
      v_8067 <- getRegister v_3029;
      v_8068 <- eval (extract v_8067 128 256);
      v_8070 <- eval (extract v_8067 0 128);
      v_8072 <- getRegister v_3028;
      v_8073 <- eval (extract v_8072 128 256);
      v_8074 <- eval (extract v_8072 0 128);
      v_8080 <- eval (extract v_8063 6 8);
      setRegister (lhs.of_reg v_3030) (concat (mux (isBitSet v_8063 0) (expression.bv_nat 128 0) (mux (eq v_8065 (expression.bv_nat 2 0)) v_8068 (mux (eq v_8065 (expression.bv_nat 2 1)) v_8070 (mux (eq v_8065 (expression.bv_nat 2 2)) v_8073 v_8074)))) (mux (isBitSet v_8063 4) (expression.bv_nat 128 0) (mux (eq v_8080 (expression.bv_nat 2 0)) v_8068 (mux (eq v_8080 (expression.bv_nat 2 1)) v_8070 (mux (eq v_8080 (expression.bv_nat 2 2)) v_8073 v_8074)))));
      pure ()
    pat_end;
    pattern fun (v_3022 : imm int) (v_3021 : Mem) (v_3023 : reg (bv 256)) (v_3024 : reg (bv 256)) => do
      v_16614 <- eval (handleImmediateWithSignExtend v_3022 8 8);
      v_16616 <- eval (extract v_16614 2 4);
      v_16618 <- getRegister v_3023;
      v_16619 <- eval (extract v_16618 128 256);
      v_16621 <- eval (extract v_16618 0 128);
      v_16623 <- evaluateAddress v_3021;
      v_16624 <- load v_16623 32;
      v_16625 <- eval (extract v_16624 128 256);
      v_16626 <- eval (extract v_16624 0 128);
      v_16632 <- eval (extract v_16614 6 8);
      setRegister (lhs.of_reg v_3024) (concat (mux (isBitSet v_16614 0) (expression.bv_nat 128 0) (mux (eq v_16616 (expression.bv_nat 2 0)) v_16619 (mux (eq v_16616 (expression.bv_nat 2 1)) v_16621 (mux (eq v_16616 (expression.bv_nat 2 2)) v_16625 v_16626)))) (mux (isBitSet v_16614 4) (expression.bv_nat 128 0) (mux (eq v_16632 (expression.bv_nat 2 0)) v_16619 (mux (eq v_16632 (expression.bv_nat 2 1)) v_16621 (mux (eq v_16632 (expression.bv_nat 2 2)) v_16625 v_16626)))));
      pure ()
    pat_end
