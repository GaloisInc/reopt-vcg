def phminposuw1 : instruction :=
  definst "phminposuw" $ do
    pattern fun (v_2469 : reg (bv 128)) (v_2470 : reg (bv 128)) => do
      v_4196 <- getRegister v_2469;
      v_4197 <- eval (extract v_4196 0 16);
      v_4198 <- eval (extract v_4196 16 32);
      v_4199 <- eval (extract v_4196 32 48);
      v_4200 <- eval (extract v_4196 48 64);
      v_4201 <- eval (extract v_4196 64 80);
      v_4202 <- eval (extract v_4196 80 96);
      v_4203 <- eval (extract v_4196 96 112);
      v_4204 <- eval (extract v_4196 112 128);
      v_4205 <- eval (ult v_4203 v_4204);
      v_4206 <- eval (mux v_4205 v_4203 v_4204);
      v_4207 <- eval (ult v_4202 v_4206);
      v_4208 <- eval (mux v_4207 v_4202 v_4206);
      v_4209 <- eval (ult v_4201 v_4208);
      v_4210 <- eval (mux v_4209 v_4201 v_4208);
      v_4211 <- eval (ult v_4200 v_4210);
      v_4212 <- eval (mux v_4211 v_4200 v_4210);
      v_4213 <- eval (ult v_4199 v_4212);
      v_4214 <- eval (mux v_4213 v_4199 v_4212);
      v_4215 <- eval (ult v_4198 v_4214);
      v_4216 <- eval (mux v_4215 v_4198 v_4214);
      v_4217 <- eval (ult v_4197 v_4216);
      setRegister (lhs.of_reg v_2470) (concat (mux v_4217 (expression.bv_nat 112 7) (mux v_4215 (expression.bv_nat 112 6) (mux v_4213 (expression.bv_nat 112 5) (mux v_4211 (expression.bv_nat 112 4) (mux v_4209 (expression.bv_nat 112 3) (mux v_4207 (expression.bv_nat 112 2) (mux v_4205 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_4217 v_4197 v_4216));
      pure ()
    pat_end;
    pattern fun (v_2465 : Mem) (v_2466 : reg (bv 128)) => do
      v_11321 <- evaluateAddress v_2465;
      v_11322 <- load v_11321 16;
      v_11323 <- eval (extract v_11322 0 16);
      v_11324 <- eval (extract v_11322 16 32);
      v_11325 <- eval (extract v_11322 32 48);
      v_11326 <- eval (extract v_11322 48 64);
      v_11327 <- eval (extract v_11322 64 80);
      v_11328 <- eval (extract v_11322 80 96);
      v_11329 <- eval (extract v_11322 96 112);
      v_11330 <- eval (extract v_11322 112 128);
      v_11331 <- eval (ult v_11329 v_11330);
      v_11332 <- eval (mux v_11331 v_11329 v_11330);
      v_11333 <- eval (ult v_11328 v_11332);
      v_11334 <- eval (mux v_11333 v_11328 v_11332);
      v_11335 <- eval (ult v_11327 v_11334);
      v_11336 <- eval (mux v_11335 v_11327 v_11334);
      v_11337 <- eval (ult v_11326 v_11336);
      v_11338 <- eval (mux v_11337 v_11326 v_11336);
      v_11339 <- eval (ult v_11325 v_11338);
      v_11340 <- eval (mux v_11339 v_11325 v_11338);
      v_11341 <- eval (ult v_11324 v_11340);
      v_11342 <- eval (mux v_11341 v_11324 v_11340);
      v_11343 <- eval (ult v_11323 v_11342);
      setRegister (lhs.of_reg v_2466) (concat (mux v_11343 (expression.bv_nat 112 7) (mux v_11341 (expression.bv_nat 112 6) (mux v_11339 (expression.bv_nat 112 5) (mux v_11337 (expression.bv_nat 112 4) (mux v_11335 (expression.bv_nat 112 3) (mux v_11333 (expression.bv_nat 112 2) (mux v_11331 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_11343 v_11323 v_11342));
      pure ()
    pat_end
