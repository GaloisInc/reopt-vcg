def pabsb1 : instruction :=
  definst "pabsb" $ do
    pattern fun (v_3060 : reg (bv 128)) (v_3061 : reg (bv 128)) => do
      v_5162 <- getRegister v_3060;
      v_5163 <- eval (extract v_5162 0 8);
      v_5168 <- eval (extract v_5162 8 16);
      v_5173 <- eval (extract v_5162 16 24);
      v_5178 <- eval (extract v_5162 24 32);
      v_5183 <- eval (extract v_5162 32 40);
      v_5188 <- eval (extract v_5162 40 48);
      v_5193 <- eval (extract v_5162 48 56);
      v_5198 <- eval (extract v_5162 56 64);
      v_5203 <- eval (extract v_5162 64 72);
      v_5208 <- eval (extract v_5162 72 80);
      v_5213 <- eval (extract v_5162 80 88);
      v_5218 <- eval (extract v_5162 88 96);
      v_5223 <- eval (extract v_5162 96 104);
      v_5228 <- eval (extract v_5162 104 112);
      v_5233 <- eval (extract v_5162 112 120);
      v_5238 <- eval (extract v_5162 120 128);
      setRegister (lhs.of_reg v_3061) (concat (mux (ugt v_5163 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5163 (expression.bv_nat 8 255))) v_5163) (concat (mux (ugt v_5168 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5168 (expression.bv_nat 8 255))) v_5168) (concat (mux (ugt v_5173 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5173 (expression.bv_nat 8 255))) v_5173) (concat (mux (ugt v_5178 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5178 (expression.bv_nat 8 255))) v_5178) (concat (mux (ugt v_5183 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5183 (expression.bv_nat 8 255))) v_5183) (concat (mux (ugt v_5188 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5188 (expression.bv_nat 8 255))) v_5188) (concat (mux (ugt v_5193 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5193 (expression.bv_nat 8 255))) v_5193) (concat (mux (ugt v_5198 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5198 (expression.bv_nat 8 255))) v_5198) (concat (mux (ugt v_5203 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5203 (expression.bv_nat 8 255))) v_5203) (concat (mux (ugt v_5208 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5208 (expression.bv_nat 8 255))) v_5208) (concat (mux (ugt v_5213 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5213 (expression.bv_nat 8 255))) v_5213) (concat (mux (ugt v_5218 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5218 (expression.bv_nat 8 255))) v_5218) (concat (mux (ugt v_5223 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5223 (expression.bv_nat 8 255))) v_5223) (concat (mux (ugt v_5228 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5228 (expression.bv_nat 8 255))) v_5228) (concat (mux (ugt v_5233 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5233 (expression.bv_nat 8 255))) v_5233) (mux (ugt v_5238 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5238 (expression.bv_nat 8 255))) v_5238))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3056 : Mem) (v_3057 : reg (bv 128)) => do
      v_9267 <- evaluateAddress v_3056;
      v_9268 <- load v_9267 16;
      v_9269 <- eval (extract v_9268 0 8);
      v_9274 <- eval (extract v_9268 8 16);
      v_9279 <- eval (extract v_9268 16 24);
      v_9284 <- eval (extract v_9268 24 32);
      v_9289 <- eval (extract v_9268 32 40);
      v_9294 <- eval (extract v_9268 40 48);
      v_9299 <- eval (extract v_9268 48 56);
      v_9304 <- eval (extract v_9268 56 64);
      v_9309 <- eval (extract v_9268 64 72);
      v_9314 <- eval (extract v_9268 72 80);
      v_9319 <- eval (extract v_9268 80 88);
      v_9324 <- eval (extract v_9268 88 96);
      v_9329 <- eval (extract v_9268 96 104);
      v_9334 <- eval (extract v_9268 104 112);
      v_9339 <- eval (extract v_9268 112 120);
      v_9344 <- eval (extract v_9268 120 128);
      setRegister (lhs.of_reg v_3057) (concat (mux (ugt v_9269 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9269 (expression.bv_nat 8 255))) v_9269) (concat (mux (ugt v_9274 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9274 (expression.bv_nat 8 255))) v_9274) (concat (mux (ugt v_9279 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9279 (expression.bv_nat 8 255))) v_9279) (concat (mux (ugt v_9284 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9284 (expression.bv_nat 8 255))) v_9284) (concat (mux (ugt v_9289 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9289 (expression.bv_nat 8 255))) v_9289) (concat (mux (ugt v_9294 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9294 (expression.bv_nat 8 255))) v_9294) (concat (mux (ugt v_9299 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9299 (expression.bv_nat 8 255))) v_9299) (concat (mux (ugt v_9304 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9304 (expression.bv_nat 8 255))) v_9304) (concat (mux (ugt v_9309 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9309 (expression.bv_nat 8 255))) v_9309) (concat (mux (ugt v_9314 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9314 (expression.bv_nat 8 255))) v_9314) (concat (mux (ugt v_9319 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9319 (expression.bv_nat 8 255))) v_9319) (concat (mux (ugt v_9324 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9324 (expression.bv_nat 8 255))) v_9324) (concat (mux (ugt v_9329 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9329 (expression.bv_nat 8 255))) v_9329) (concat (mux (ugt v_9334 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9334 (expression.bv_nat 8 255))) v_9334) (concat (mux (ugt v_9339 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9339 (expression.bv_nat 8 255))) v_9339) (mux (ugt v_9344 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9344 (expression.bv_nat 8 255))) v_9344))))))))))))))));
      pure ()
    pat_end
