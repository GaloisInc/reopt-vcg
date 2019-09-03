def pabsb1 : instruction :=
  definst "pabsb" $ do
    pattern fun (v_3048 : reg (bv 128)) (v_3049 : reg (bv 128)) => do
      v_5075 <- getRegister v_3048;
      v_5076 <- eval (extract v_5075 0 8);
      v_5083 <- eval (extract v_5075 8 16);
      v_5090 <- eval (extract v_5075 16 24);
      v_5097 <- eval (extract v_5075 24 32);
      v_5104 <- eval (extract v_5075 32 40);
      v_5111 <- eval (extract v_5075 40 48);
      v_5118 <- eval (extract v_5075 48 56);
      v_5125 <- eval (extract v_5075 56 64);
      v_5132 <- eval (extract v_5075 64 72);
      v_5139 <- eval (extract v_5075 72 80);
      v_5146 <- eval (extract v_5075 80 88);
      v_5153 <- eval (extract v_5075 88 96);
      v_5160 <- eval (extract v_5075 96 104);
      v_5167 <- eval (extract v_5075 104 112);
      v_5174 <- eval (extract v_5075 112 120);
      v_5181 <- eval (extract v_5075 120 128);
      setRegister (lhs.of_reg v_3049) (concat (mux (ugt v_5076 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5076 (mi (bitwidthMInt v_5076) -1))) v_5076) (concat (mux (ugt v_5083 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5083 (mi (bitwidthMInt v_5083) -1))) v_5083) (concat (mux (ugt v_5090 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5090 (mi (bitwidthMInt v_5090) -1))) v_5090) (concat (mux (ugt v_5097 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5097 (mi (bitwidthMInt v_5097) -1))) v_5097) (concat (mux (ugt v_5104 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5104 (mi (bitwidthMInt v_5104) -1))) v_5104) (concat (mux (ugt v_5111 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5111 (mi (bitwidthMInt v_5111) -1))) v_5111) (concat (mux (ugt v_5118 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5118 (mi (bitwidthMInt v_5118) -1))) v_5118) (concat (mux (ugt v_5125 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5125 (mi (bitwidthMInt v_5125) -1))) v_5125) (concat (mux (ugt v_5132 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5132 (mi (bitwidthMInt v_5132) -1))) v_5132) (concat (mux (ugt v_5139 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5139 (mi (bitwidthMInt v_5139) -1))) v_5139) (concat (mux (ugt v_5146 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5146 (mi (bitwidthMInt v_5146) -1))) v_5146) (concat (mux (ugt v_5153 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5153 (mi (bitwidthMInt v_5153) -1))) v_5153) (concat (mux (ugt v_5160 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5160 (mi (bitwidthMInt v_5160) -1))) v_5160) (concat (mux (ugt v_5167 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5167 (mi (bitwidthMInt v_5167) -1))) v_5167) (concat (mux (ugt v_5174 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5174 (mi (bitwidthMInt v_5174) -1))) v_5174) (mux (ugt v_5181 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5181 (mi (bitwidthMInt v_5181) -1))) v_5181))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3043 : Mem) (v_3044 : reg (bv 128)) => do
      v_9192 <- evaluateAddress v_3043;
      v_9193 <- load v_9192 16;
      v_9194 <- eval (extract v_9193 0 8);
      v_9201 <- eval (extract v_9193 8 16);
      v_9208 <- eval (extract v_9193 16 24);
      v_9215 <- eval (extract v_9193 24 32);
      v_9222 <- eval (extract v_9193 32 40);
      v_9229 <- eval (extract v_9193 40 48);
      v_9236 <- eval (extract v_9193 48 56);
      v_9243 <- eval (extract v_9193 56 64);
      v_9250 <- eval (extract v_9193 64 72);
      v_9257 <- eval (extract v_9193 72 80);
      v_9264 <- eval (extract v_9193 80 88);
      v_9271 <- eval (extract v_9193 88 96);
      v_9278 <- eval (extract v_9193 96 104);
      v_9285 <- eval (extract v_9193 104 112);
      v_9292 <- eval (extract v_9193 112 120);
      v_9299 <- eval (extract v_9193 120 128);
      setRegister (lhs.of_reg v_3044) (concat (mux (ugt v_9194 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9194 (mi (bitwidthMInt v_9194) -1))) v_9194) (concat (mux (ugt v_9201 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9201 (mi (bitwidthMInt v_9201) -1))) v_9201) (concat (mux (ugt v_9208 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9208 (mi (bitwidthMInt v_9208) -1))) v_9208) (concat (mux (ugt v_9215 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9215 (mi (bitwidthMInt v_9215) -1))) v_9215) (concat (mux (ugt v_9222 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9222 (mi (bitwidthMInt v_9222) -1))) v_9222) (concat (mux (ugt v_9229 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9229 (mi (bitwidthMInt v_9229) -1))) v_9229) (concat (mux (ugt v_9236 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9236 (mi (bitwidthMInt v_9236) -1))) v_9236) (concat (mux (ugt v_9243 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9243 (mi (bitwidthMInt v_9243) -1))) v_9243) (concat (mux (ugt v_9250 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9250 (mi (bitwidthMInt v_9250) -1))) v_9250) (concat (mux (ugt v_9257 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9257 (mi (bitwidthMInt v_9257) -1))) v_9257) (concat (mux (ugt v_9264 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9264 (mi (bitwidthMInt v_9264) -1))) v_9264) (concat (mux (ugt v_9271 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9271 (mi (bitwidthMInt v_9271) -1))) v_9271) (concat (mux (ugt v_9278 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9278 (mi (bitwidthMInt v_9278) -1))) v_9278) (concat (mux (ugt v_9285 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9285 (mi (bitwidthMInt v_9285) -1))) v_9285) (concat (mux (ugt v_9292 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9292 (mi (bitwidthMInt v_9292) -1))) v_9292) (mux (ugt v_9299 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9299 (mi (bitwidthMInt v_9299) -1))) v_9299))))))))))))))));
      pure ()
    pat_end
