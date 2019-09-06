def phminposuw1 : instruction :=
  definst "phminposuw" $ do
    pattern fun (v_2546 : reg (bv 128)) (v_2547 : reg (bv 128)) => do
      v_4274 <- getRegister v_2546;
      v_4275 <- eval (extract v_4274 0 16);
      v_4276 <- eval (extract v_4274 16 32);
      v_4277 <- eval (extract v_4274 32 48);
      v_4278 <- eval (extract v_4274 48 64);
      v_4279 <- eval (extract v_4274 64 80);
      v_4280 <- eval (extract v_4274 80 96);
      v_4281 <- eval (extract v_4274 96 112);
      v_4282 <- eval (extract v_4274 112 128);
      v_4283 <- eval (ult v_4281 v_4282);
      v_4284 <- eval (mux v_4283 v_4281 v_4282);
      v_4285 <- eval (ult v_4280 v_4284);
      v_4286 <- eval (mux v_4285 v_4280 v_4284);
      v_4287 <- eval (ult v_4279 v_4286);
      v_4288 <- eval (mux v_4287 v_4279 v_4286);
      v_4289 <- eval (ult v_4278 v_4288);
      v_4290 <- eval (mux v_4289 v_4278 v_4288);
      v_4291 <- eval (ult v_4277 v_4290);
      v_4292 <- eval (mux v_4291 v_4277 v_4290);
      v_4293 <- eval (ult v_4276 v_4292);
      v_4294 <- eval (mux v_4293 v_4276 v_4292);
      v_4295 <- eval (ult v_4275 v_4294);
      setRegister (lhs.of_reg v_2547) (concat (mux v_4295 (expression.bv_nat 112 7) (mux v_4293 (expression.bv_nat 112 6) (mux v_4291 (expression.bv_nat 112 5) (mux v_4289 (expression.bv_nat 112 4) (mux v_4287 (expression.bv_nat 112 3) (mux v_4285 (expression.bv_nat 112 2) (mux v_4283 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_4295 v_4275 v_4294));
      pure ()
    pat_end;
    pattern fun (v_2542 : Mem) (v_2543 : reg (bv 128)) => do
      v_11174 <- evaluateAddress v_2542;
      v_11175 <- load v_11174 16;
      v_11176 <- eval (extract v_11175 0 16);
      v_11177 <- eval (extract v_11175 16 32);
      v_11178 <- eval (extract v_11175 32 48);
      v_11179 <- eval (extract v_11175 48 64);
      v_11180 <- eval (extract v_11175 64 80);
      v_11181 <- eval (extract v_11175 80 96);
      v_11182 <- eval (extract v_11175 96 112);
      v_11183 <- eval (extract v_11175 112 128);
      v_11184 <- eval (ult v_11182 v_11183);
      v_11185 <- eval (mux v_11184 v_11182 v_11183);
      v_11186 <- eval (ult v_11181 v_11185);
      v_11187 <- eval (mux v_11186 v_11181 v_11185);
      v_11188 <- eval (ult v_11180 v_11187);
      v_11189 <- eval (mux v_11188 v_11180 v_11187);
      v_11190 <- eval (ult v_11179 v_11189);
      v_11191 <- eval (mux v_11190 v_11179 v_11189);
      v_11192 <- eval (ult v_11178 v_11191);
      v_11193 <- eval (mux v_11192 v_11178 v_11191);
      v_11194 <- eval (ult v_11177 v_11193);
      v_11195 <- eval (mux v_11194 v_11177 v_11193);
      v_11196 <- eval (ult v_11176 v_11195);
      setRegister (lhs.of_reg v_2543) (concat (mux v_11196 (expression.bv_nat 112 7) (mux v_11194 (expression.bv_nat 112 6) (mux v_11192 (expression.bv_nat 112 5) (mux v_11190 (expression.bv_nat 112 4) (mux v_11188 (expression.bv_nat 112 3) (mux v_11186 (expression.bv_nat 112 2) (mux v_11184 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_11196 v_11176 v_11195));
      pure ()
    pat_end
