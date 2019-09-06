def pabsb1 : instruction :=
  definst "pabsb" $ do
    pattern fun (v_3136 : reg (bv 128)) (v_3137 : reg (bv 128)) => do
      v_5102 <- getRegister v_3136;
      v_5103 <- eval (extract v_5102 0 8);
      v_5108 <- eval (extract v_5102 8 16);
      v_5113 <- eval (extract v_5102 16 24);
      v_5118 <- eval (extract v_5102 24 32);
      v_5123 <- eval (extract v_5102 32 40);
      v_5128 <- eval (extract v_5102 40 48);
      v_5133 <- eval (extract v_5102 48 56);
      v_5138 <- eval (extract v_5102 56 64);
      v_5143 <- eval (extract v_5102 64 72);
      v_5148 <- eval (extract v_5102 72 80);
      v_5153 <- eval (extract v_5102 80 88);
      v_5158 <- eval (extract v_5102 88 96);
      v_5163 <- eval (extract v_5102 96 104);
      v_5168 <- eval (extract v_5102 104 112);
      v_5173 <- eval (extract v_5102 112 120);
      v_5178 <- eval (extract v_5102 120 128);
      setRegister (lhs.of_reg v_3137) (concat (mux (ugt v_5103 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5103 (expression.bv_nat 8 255))) v_5103) (concat (mux (ugt v_5108 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5108 (expression.bv_nat 8 255))) v_5108) (concat (mux (ugt v_5113 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5113 (expression.bv_nat 8 255))) v_5113) (concat (mux (ugt v_5118 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5118 (expression.bv_nat 8 255))) v_5118) (concat (mux (ugt v_5123 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5123 (expression.bv_nat 8 255))) v_5123) (concat (mux (ugt v_5128 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5128 (expression.bv_nat 8 255))) v_5128) (concat (mux (ugt v_5133 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5133 (expression.bv_nat 8 255))) v_5133) (concat (mux (ugt v_5138 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5138 (expression.bv_nat 8 255))) v_5138) (concat (mux (ugt v_5143 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5143 (expression.bv_nat 8 255))) v_5143) (concat (mux (ugt v_5148 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5148 (expression.bv_nat 8 255))) v_5148) (concat (mux (ugt v_5153 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5153 (expression.bv_nat 8 255))) v_5153) (concat (mux (ugt v_5158 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5158 (expression.bv_nat 8 255))) v_5158) (concat (mux (ugt v_5163 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5163 (expression.bv_nat 8 255))) v_5163) (concat (mux (ugt v_5168 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5168 (expression.bv_nat 8 255))) v_5168) (concat (mux (ugt v_5173 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5173 (expression.bv_nat 8 255))) v_5173) (mux (ugt v_5178 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5178 (expression.bv_nat 8 255))) v_5178))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3132 : Mem) (v_3133 : reg (bv 128)) => do
      v_9058 <- evaluateAddress v_3132;
      v_9059 <- load v_9058 16;
      v_9060 <- eval (extract v_9059 0 8);
      v_9065 <- eval (extract v_9059 8 16);
      v_9070 <- eval (extract v_9059 16 24);
      v_9075 <- eval (extract v_9059 24 32);
      v_9080 <- eval (extract v_9059 32 40);
      v_9085 <- eval (extract v_9059 40 48);
      v_9090 <- eval (extract v_9059 48 56);
      v_9095 <- eval (extract v_9059 56 64);
      v_9100 <- eval (extract v_9059 64 72);
      v_9105 <- eval (extract v_9059 72 80);
      v_9110 <- eval (extract v_9059 80 88);
      v_9115 <- eval (extract v_9059 88 96);
      v_9120 <- eval (extract v_9059 96 104);
      v_9125 <- eval (extract v_9059 104 112);
      v_9130 <- eval (extract v_9059 112 120);
      v_9135 <- eval (extract v_9059 120 128);
      setRegister (lhs.of_reg v_3133) (concat (mux (ugt v_9060 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9060 (expression.bv_nat 8 255))) v_9060) (concat (mux (ugt v_9065 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9065 (expression.bv_nat 8 255))) v_9065) (concat (mux (ugt v_9070 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9070 (expression.bv_nat 8 255))) v_9070) (concat (mux (ugt v_9075 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9075 (expression.bv_nat 8 255))) v_9075) (concat (mux (ugt v_9080 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9080 (expression.bv_nat 8 255))) v_9080) (concat (mux (ugt v_9085 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9085 (expression.bv_nat 8 255))) v_9085) (concat (mux (ugt v_9090 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9090 (expression.bv_nat 8 255))) v_9090) (concat (mux (ugt v_9095 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9095 (expression.bv_nat 8 255))) v_9095) (concat (mux (ugt v_9100 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9100 (expression.bv_nat 8 255))) v_9100) (concat (mux (ugt v_9105 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9105 (expression.bv_nat 8 255))) v_9105) (concat (mux (ugt v_9110 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9110 (expression.bv_nat 8 255))) v_9110) (concat (mux (ugt v_9115 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9115 (expression.bv_nat 8 255))) v_9115) (concat (mux (ugt v_9120 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9120 (expression.bv_nat 8 255))) v_9120) (concat (mux (ugt v_9125 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9125 (expression.bv_nat 8 255))) v_9125) (concat (mux (ugt v_9130 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9130 (expression.bv_nat 8 255))) v_9130) (mux (ugt v_9135 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9135 (expression.bv_nat 8 255))) v_9135))))))))))))))));
      pure ()
    pat_end
