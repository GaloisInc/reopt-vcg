def vperm2i1281 : instruction :=
  definst "vperm2i128" $ do
    pattern fun (v_3040 : imm int) (v_3041 : reg (bv 256)) (v_3042 : reg (bv 256)) (v_3043 : reg (bv 256)) => do
      v_8096 <- eval (handleImmediateWithSignExtend v_3040 8 8);
      v_8098 <- eval (extract v_8096 2 4);
      v_8100 <- getRegister v_3042;
      v_8101 <- eval (extract v_8100 128 256);
      v_8103 <- eval (extract v_8100 0 128);
      v_8105 <- getRegister v_3041;
      v_8106 <- eval (extract v_8105 128 256);
      v_8107 <- eval (extract v_8105 0 128);
      v_8113 <- eval (extract v_8096 6 8);
      setRegister (lhs.of_reg v_3043) (concat (mux (isBitSet v_8096 0) (expression.bv_nat 128 0) (mux (eq v_8098 (expression.bv_nat 2 0)) v_8101 (mux (eq v_8098 (expression.bv_nat 2 1)) v_8103 (mux (eq v_8098 (expression.bv_nat 2 2)) v_8106 v_8107)))) (mux (isBitSet v_8096 4) (expression.bv_nat 128 0) (mux (eq v_8113 (expression.bv_nat 2 0)) v_8101 (mux (eq v_8113 (expression.bv_nat 2 1)) v_8103 (mux (eq v_8113 (expression.bv_nat 2 2)) v_8106 v_8107)))));
      pure ()
    pat_end;
    pattern fun (v_3035 : imm int) (v_3034 : Mem) (v_3036 : reg (bv 256)) (v_3037 : reg (bv 256)) => do
      v_16642 <- eval (handleImmediateWithSignExtend v_3035 8 8);
      v_16644 <- eval (extract v_16642 2 4);
      v_16646 <- getRegister v_3036;
      v_16647 <- eval (extract v_16646 128 256);
      v_16649 <- eval (extract v_16646 0 128);
      v_16651 <- evaluateAddress v_3034;
      v_16652 <- load v_16651 32;
      v_16653 <- eval (extract v_16652 128 256);
      v_16654 <- eval (extract v_16652 0 128);
      v_16660 <- eval (extract v_16642 6 8);
      setRegister (lhs.of_reg v_3037) (concat (mux (isBitSet v_16642 0) (expression.bv_nat 128 0) (mux (eq v_16644 (expression.bv_nat 2 0)) v_16647 (mux (eq v_16644 (expression.bv_nat 2 1)) v_16649 (mux (eq v_16644 (expression.bv_nat 2 2)) v_16653 v_16654)))) (mux (isBitSet v_16642 4) (expression.bv_nat 128 0) (mux (eq v_16660 (expression.bv_nat 2 0)) v_16647 (mux (eq v_16660 (expression.bv_nat 2 1)) v_16649 (mux (eq v_16660 (expression.bv_nat 2 2)) v_16653 v_16654)))));
      pure ()
    pat_end
