def pabsw1 : instruction :=
  definst "pabsw" $ do
    pattern fun (v_3154 : reg (bv 128)) (v_3155 : reg (bv 128)) => do
      v_5232 <- getRegister v_3154;
      v_5233 <- eval (extract v_5232 0 16);
      v_5238 <- eval (extract v_5232 16 32);
      v_5243 <- eval (extract v_5232 32 48);
      v_5248 <- eval (extract v_5232 48 64);
      v_5253 <- eval (extract v_5232 64 80);
      v_5258 <- eval (extract v_5232 80 96);
      v_5263 <- eval (extract v_5232 96 112);
      v_5268 <- eval (extract v_5232 112 128);
      setRegister (lhs.of_reg v_3155) (concat (mux (ugt v_5233 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5233 (expression.bv_nat 16 65535))) v_5233) (concat (mux (ugt v_5238 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5238 (expression.bv_nat 16 65535))) v_5238) (concat (mux (ugt v_5243 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5243 (expression.bv_nat 16 65535))) v_5243) (concat (mux (ugt v_5248 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5248 (expression.bv_nat 16 65535))) v_5248) (concat (mux (ugt v_5253 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5253 (expression.bv_nat 16 65535))) v_5253) (concat (mux (ugt v_5258 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5258 (expression.bv_nat 16 65535))) v_5258) (concat (mux (ugt v_5263 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5263 (expression.bv_nat 16 65535))) v_5263) (mux (ugt v_5268 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5268 (expression.bv_nat 16 65535))) v_5268))))))));
      pure ()
    pat_end;
    pattern fun (v_3150 : Mem) (v_3151 : reg (bv 128)) => do
      v_9182 <- evaluateAddress v_3150;
      v_9183 <- load v_9182 16;
      v_9184 <- eval (extract v_9183 0 16);
      v_9189 <- eval (extract v_9183 16 32);
      v_9194 <- eval (extract v_9183 32 48);
      v_9199 <- eval (extract v_9183 48 64);
      v_9204 <- eval (extract v_9183 64 80);
      v_9209 <- eval (extract v_9183 80 96);
      v_9214 <- eval (extract v_9183 96 112);
      v_9219 <- eval (extract v_9183 112 128);
      setRegister (lhs.of_reg v_3151) (concat (mux (ugt v_9184 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9184 (expression.bv_nat 16 65535))) v_9184) (concat (mux (ugt v_9189 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9189 (expression.bv_nat 16 65535))) v_9189) (concat (mux (ugt v_9194 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9194 (expression.bv_nat 16 65535))) v_9194) (concat (mux (ugt v_9199 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9199 (expression.bv_nat 16 65535))) v_9199) (concat (mux (ugt v_9204 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9204 (expression.bv_nat 16 65535))) v_9204) (concat (mux (ugt v_9209 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9209 (expression.bv_nat 16 65535))) v_9209) (concat (mux (ugt v_9214 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9214 (expression.bv_nat 16 65535))) v_9214) (mux (ugt v_9219 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9219 (expression.bv_nat 16 65535))) v_9219))))))));
      pure ()
    pat_end
