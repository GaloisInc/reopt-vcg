def vpsignw1 : instruction :=
  definst "vpsignw" $ do
    pattern fun (v_3040 : reg (bv 128)) (v_3041 : reg (bv 128)) (v_3042 : reg (bv 128)) => do
      v_7524 <- getRegister v_3040;
      v_7525 <- eval (extract v_7524 0 16);
      v_7527 <- getRegister v_3041;
      v_7528 <- eval (extract v_7527 0 16);
      v_7534 <- eval (extract v_7524 16 32);
      v_7536 <- eval (extract v_7527 16 32);
      v_7542 <- eval (extract v_7524 32 48);
      v_7544 <- eval (extract v_7527 32 48);
      v_7550 <- eval (extract v_7524 48 64);
      v_7552 <- eval (extract v_7527 48 64);
      v_7558 <- eval (extract v_7524 64 80);
      v_7560 <- eval (extract v_7527 64 80);
      v_7566 <- eval (extract v_7524 80 96);
      v_7568 <- eval (extract v_7527 80 96);
      v_7574 <- eval (extract v_7524 96 112);
      v_7576 <- eval (extract v_7527 96 112);
      v_7582 <- eval (extract v_7524 112 128);
      v_7584 <- eval (extract v_7527 112 128);
      setRegister (lhs.of_reg v_3042) (concat (mux (sgt v_7525 (expression.bv_nat 16 0)) v_7528 (mux (eq v_7525 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7528 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7534 (expression.bv_nat 16 0)) v_7536 (mux (eq v_7534 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7536 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7542 (expression.bv_nat 16 0)) v_7544 (mux (eq v_7542 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7544 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7550 (expression.bv_nat 16 0)) v_7552 (mux (eq v_7550 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7552 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7558 (expression.bv_nat 16 0)) v_7560 (mux (eq v_7558 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7560 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7566 (expression.bv_nat 16 0)) v_7568 (mux (eq v_7566 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7568 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7574 (expression.bv_nat 16 0)) v_7576 (mux (eq v_7574 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7576 (expression.bv_nat 16 65535))))) (mux (sgt v_7582 (expression.bv_nat 16 0)) v_7584 (mux (eq v_7582 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7584 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3034 : Mem) (v_3035 : reg (bv 128)) (v_3036 : reg (bv 128)) => do
      v_14058 <- evaluateAddress v_3034;
      v_14059 <- load v_14058 16;
      v_14060 <- eval (extract v_14059 0 16);
      v_14062 <- getRegister v_3035;
      v_14063 <- eval (extract v_14062 0 16);
      v_14069 <- eval (extract v_14059 16 32);
      v_14071 <- eval (extract v_14062 16 32);
      v_14077 <- eval (extract v_14059 32 48);
      v_14079 <- eval (extract v_14062 32 48);
      v_14085 <- eval (extract v_14059 48 64);
      v_14087 <- eval (extract v_14062 48 64);
      v_14093 <- eval (extract v_14059 64 80);
      v_14095 <- eval (extract v_14062 64 80);
      v_14101 <- eval (extract v_14059 80 96);
      v_14103 <- eval (extract v_14062 80 96);
      v_14109 <- eval (extract v_14059 96 112);
      v_14111 <- eval (extract v_14062 96 112);
      v_14117 <- eval (extract v_14059 112 128);
      v_14119 <- eval (extract v_14062 112 128);
      setRegister (lhs.of_reg v_3036) (concat (mux (sgt v_14060 (expression.bv_nat 16 0)) v_14063 (mux (eq v_14060 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14063 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14069 (expression.bv_nat 16 0)) v_14071 (mux (eq v_14069 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14071 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14077 (expression.bv_nat 16 0)) v_14079 (mux (eq v_14077 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14079 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14085 (expression.bv_nat 16 0)) v_14087 (mux (eq v_14085 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14087 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14093 (expression.bv_nat 16 0)) v_14095 (mux (eq v_14093 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14095 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14101 (expression.bv_nat 16 0)) v_14103 (mux (eq v_14101 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14103 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14109 (expression.bv_nat 16 0)) v_14111 (mux (eq v_14109 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14111 (expression.bv_nat 16 65535))))) (mux (sgt v_14117 (expression.bv_nat 16 0)) v_14119 (mux (eq v_14117 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14119 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end
