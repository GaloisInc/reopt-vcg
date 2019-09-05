def phminposuw1 : instruction :=
  definst "phminposuw" $ do
    pattern fun (v_2518 : reg (bv 128)) (v_2519 : reg (bv 128)) => do
      v_4247 <- getRegister v_2518;
      v_4248 <- eval (extract v_4247 0 16);
      v_4249 <- eval (extract v_4247 16 32);
      v_4250 <- eval (extract v_4247 32 48);
      v_4251 <- eval (extract v_4247 48 64);
      v_4252 <- eval (extract v_4247 64 80);
      v_4253 <- eval (extract v_4247 80 96);
      v_4254 <- eval (extract v_4247 96 112);
      v_4255 <- eval (extract v_4247 112 128);
      v_4256 <- eval (ult v_4254 v_4255);
      v_4257 <- eval (mux v_4256 v_4254 v_4255);
      v_4258 <- eval (ult v_4253 v_4257);
      v_4259 <- eval (mux v_4258 v_4253 v_4257);
      v_4260 <- eval (ult v_4252 v_4259);
      v_4261 <- eval (mux v_4260 v_4252 v_4259);
      v_4262 <- eval (ult v_4251 v_4261);
      v_4263 <- eval (mux v_4262 v_4251 v_4261);
      v_4264 <- eval (ult v_4250 v_4263);
      v_4265 <- eval (mux v_4264 v_4250 v_4263);
      v_4266 <- eval (ult v_4249 v_4265);
      v_4267 <- eval (mux v_4266 v_4249 v_4265);
      v_4268 <- eval (ult v_4248 v_4267);
      setRegister (lhs.of_reg v_2519) (concat (mux v_4268 (expression.bv_nat 112 7) (mux v_4266 (expression.bv_nat 112 6) (mux v_4264 (expression.bv_nat 112 5) (mux v_4262 (expression.bv_nat 112 4) (mux v_4260 (expression.bv_nat 112 3) (mux v_4258 (expression.bv_nat 112 2) (mux v_4256 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_4268 v_4248 v_4267));
      pure ()
    pat_end;
    pattern fun (v_2515 : Mem) (v_2514 : reg (bv 128)) => do
      v_11198 <- evaluateAddress v_2515;
      v_11199 <- load v_11198 16;
      v_11200 <- eval (extract v_11199 0 16);
      v_11201 <- eval (extract v_11199 16 32);
      v_11202 <- eval (extract v_11199 32 48);
      v_11203 <- eval (extract v_11199 48 64);
      v_11204 <- eval (extract v_11199 64 80);
      v_11205 <- eval (extract v_11199 80 96);
      v_11206 <- eval (extract v_11199 96 112);
      v_11207 <- eval (extract v_11199 112 128);
      v_11208 <- eval (ult v_11206 v_11207);
      v_11209 <- eval (mux v_11208 v_11206 v_11207);
      v_11210 <- eval (ult v_11205 v_11209);
      v_11211 <- eval (mux v_11210 v_11205 v_11209);
      v_11212 <- eval (ult v_11204 v_11211);
      v_11213 <- eval (mux v_11212 v_11204 v_11211);
      v_11214 <- eval (ult v_11203 v_11213);
      v_11215 <- eval (mux v_11214 v_11203 v_11213);
      v_11216 <- eval (ult v_11202 v_11215);
      v_11217 <- eval (mux v_11216 v_11202 v_11215);
      v_11218 <- eval (ult v_11201 v_11217);
      v_11219 <- eval (mux v_11218 v_11201 v_11217);
      v_11220 <- eval (ult v_11200 v_11219);
      setRegister (lhs.of_reg v_2514) (concat (mux v_11220 (expression.bv_nat 112 7) (mux v_11218 (expression.bv_nat 112 6) (mux v_11216 (expression.bv_nat 112 5) (mux v_11214 (expression.bv_nat 112 4) (mux v_11212 (expression.bv_nat 112 3) (mux v_11210 (expression.bv_nat 112 2) (mux v_11208 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_11220 v_11200 v_11219));
      pure ()
    pat_end
