def vpsignd1 : instruction :=
  definst "vpsignd" $ do
    pattern fun (v_3017 : reg (bv 128)) (v_3018 : reg (bv 128)) (v_3019 : reg (bv 128)) => do
      v_7746 <- getRegister v_3017;
      v_7747 <- eval (extract v_7746 0 32);
      v_7749 <- getRegister v_3018;
      v_7750 <- eval (extract v_7749 0 32);
      v_7758 <- eval (extract v_7746 32 64);
      v_7760 <- eval (extract v_7749 32 64);
      v_7768 <- eval (extract v_7746 64 96);
      v_7770 <- eval (extract v_7749 64 96);
      v_7778 <- eval (extract v_7746 96 128);
      v_7780 <- eval (extract v_7749 96 128);
      setRegister (lhs.of_reg v_3019) (concat (mux (sgt v_7747 (expression.bv_nat 32 0)) v_7750 (mux (eq v_7747 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7750 (mi (bitwidthMInt v_7750) -1))))) (concat (mux (sgt v_7758 (expression.bv_nat 32 0)) v_7760 (mux (eq v_7758 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7760 (mi (bitwidthMInt v_7760) -1))))) (concat (mux (sgt v_7768 (expression.bv_nat 32 0)) v_7770 (mux (eq v_7768 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7770 (mi (bitwidthMInt v_7770) -1))))) (mux (sgt v_7778 (expression.bv_nat 32 0)) v_7780 (mux (eq v_7778 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_7780 (mi (bitwidthMInt v_7780) -1))))))));
      pure ()
    pat_end;
    pattern fun (v_3014 : Mem) (v_3012 : reg (bv 128)) (v_3013 : reg (bv 128)) => do
      v_14775 <- evaluateAddress v_3014;
      v_14776 <- load v_14775 16;
      v_14777 <- eval (extract v_14776 0 32);
      v_14779 <- getRegister v_3012;
      v_14780 <- eval (extract v_14779 0 32);
      v_14788 <- eval (extract v_14776 32 64);
      v_14790 <- eval (extract v_14779 32 64);
      v_14798 <- eval (extract v_14776 64 96);
      v_14800 <- eval (extract v_14779 64 96);
      v_14808 <- eval (extract v_14776 96 128);
      v_14810 <- eval (extract v_14779 96 128);
      setRegister (lhs.of_reg v_3013) (concat (mux (sgt v_14777 (expression.bv_nat 32 0)) v_14780 (mux (eq v_14777 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14780 (mi (bitwidthMInt v_14780) -1))))) (concat (mux (sgt v_14788 (expression.bv_nat 32 0)) v_14790 (mux (eq v_14788 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14790 (mi (bitwidthMInt v_14790) -1))))) (concat (mux (sgt v_14798 (expression.bv_nat 32 0)) v_14800 (mux (eq v_14798 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14800 (mi (bitwidthMInt v_14800) -1))))) (mux (sgt v_14808 (expression.bv_nat 32 0)) v_14810 (mux (eq v_14808 (expression.bv_nat 32 0)) (expression.bv_nat 32 0) (add (expression.bv_nat 32 1) (bv_xor v_14810 (mi (bitwidthMInt v_14810) -1))))))));
      pure ()
    pat_end
