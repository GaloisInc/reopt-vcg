def vfmadd231ps1 : instruction :=
  definst "vfmadd231ps" $ do
    pattern fun (v_2585 : reg (bv 128)) (v_2586 : reg (bv 128)) (v_2587 : reg (bv 128)) => do
      v_5200 <- getRegister v_2586;
      v_5201 <- eval (extract v_5200 0 32);
      v_5209 <- getRegister v_2585;
      v_5210 <- eval (extract v_5209 0 32);
      v_5219 <- getRegister v_2587;
      v_5220 <- eval (extract v_5219 0 32);
      v_5230 <- eval (extract v_5200 32 64);
      v_5238 <- eval (extract v_5209 32 64);
      v_5247 <- eval (extract v_5219 32 64);
      v_5257 <- eval (extract v_5200 64 96);
      v_5265 <- eval (extract v_5209 64 96);
      v_5274 <- eval (extract v_5219 64 96);
      v_5284 <- eval (extract v_5200 96 128);
      v_5292 <- eval (extract v_5209 96 128);
      v_5301 <- eval (extract v_5219 96 128);
      setRegister (lhs.of_reg v_2587) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5201 0 1)) (uvalueMInt (extract v_5201 1 9)) (uvalueMInt (extract v_5201 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5210 0 1)) (uvalueMInt (extract v_5210 1 9)) (uvalueMInt (extract v_5210 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5220 0 1)) (uvalueMInt (extract v_5220 1 9)) (uvalueMInt (extract v_5220 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5230 0 1)) (uvalueMInt (extract v_5230 1 9)) (uvalueMInt (extract v_5230 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5238 0 1)) (uvalueMInt (extract v_5238 1 9)) (uvalueMInt (extract v_5238 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5247 0 1)) (uvalueMInt (extract v_5247 1 9)) (uvalueMInt (extract v_5247 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5257 0 1)) (uvalueMInt (extract v_5257 1 9)) (uvalueMInt (extract v_5257 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5265 0 1)) (uvalueMInt (extract v_5265 1 9)) (uvalueMInt (extract v_5265 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5274 0 1)) (uvalueMInt (extract v_5274 1 9)) (uvalueMInt (extract v_5274 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5284 0 1)) (uvalueMInt (extract v_5284 1 9)) (uvalueMInt (extract v_5284 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5292 0 1)) (uvalueMInt (extract v_5292 1 9)) (uvalueMInt (extract v_5292 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5301 0 1)) (uvalueMInt (extract v_5301 1 9)) (uvalueMInt (extract v_5301 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2596 : reg (bv 256)) (v_2597 : reg (bv 256)) (v_2598 : reg (bv 256)) => do
      v_5320 <- getRegister v_2597;
      v_5321 <- eval (extract v_5320 0 32);
      v_5329 <- getRegister v_2596;
      v_5330 <- eval (extract v_5329 0 32);
      v_5339 <- getRegister v_2598;
      v_5340 <- eval (extract v_5339 0 32);
      v_5350 <- eval (extract v_5320 32 64);
      v_5358 <- eval (extract v_5329 32 64);
      v_5367 <- eval (extract v_5339 32 64);
      v_5378 <- eval (extract v_5320 64 96);
      v_5386 <- eval (extract v_5329 64 96);
      v_5395 <- eval (extract v_5339 64 96);
      v_5405 <- eval (extract v_5320 96 128);
      v_5413 <- eval (extract v_5329 96 128);
      v_5422 <- eval (extract v_5339 96 128);
      v_5433 <- eval (extract v_5320 128 160);
      v_5441 <- eval (extract v_5329 128 160);
      v_5450 <- eval (extract v_5339 128 160);
      v_5460 <- eval (extract v_5320 160 192);
      v_5468 <- eval (extract v_5329 160 192);
      v_5477 <- eval (extract v_5339 160 192);
      v_5487 <- eval (extract v_5320 192 224);
      v_5495 <- eval (extract v_5329 192 224);
      v_5504 <- eval (extract v_5339 192 224);
      v_5514 <- eval (extract v_5320 224 256);
      v_5522 <- eval (extract v_5329 224 256);
      v_5531 <- eval (extract v_5339 224 256);
      setRegister (lhs.of_reg v_2598) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5321 0 1)) (uvalueMInt (extract v_5321 1 9)) (uvalueMInt (extract v_5321 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5330 0 1)) (uvalueMInt (extract v_5330 1 9)) (uvalueMInt (extract v_5330 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5340 0 1)) (uvalueMInt (extract v_5340 1 9)) (uvalueMInt (extract v_5340 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5350 0 1)) (uvalueMInt (extract v_5350 1 9)) (uvalueMInt (extract v_5350 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5358 0 1)) (uvalueMInt (extract v_5358 1 9)) (uvalueMInt (extract v_5358 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5367 0 1)) (uvalueMInt (extract v_5367 1 9)) (uvalueMInt (extract v_5367 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5378 0 1)) (uvalueMInt (extract v_5378 1 9)) (uvalueMInt (extract v_5378 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5386 0 1)) (uvalueMInt (extract v_5386 1 9)) (uvalueMInt (extract v_5386 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5395 0 1)) (uvalueMInt (extract v_5395 1 9)) (uvalueMInt (extract v_5395 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5405 0 1)) (uvalueMInt (extract v_5405 1 9)) (uvalueMInt (extract v_5405 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5413 0 1)) (uvalueMInt (extract v_5413 1 9)) (uvalueMInt (extract v_5413 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5422 0 1)) (uvalueMInt (extract v_5422 1 9)) (uvalueMInt (extract v_5422 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5433 0 1)) (uvalueMInt (extract v_5433 1 9)) (uvalueMInt (extract v_5433 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5441 0 1)) (uvalueMInt (extract v_5441 1 9)) (uvalueMInt (extract v_5441 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5450 0 1)) (uvalueMInt (extract v_5450 1 9)) (uvalueMInt (extract v_5450 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5460 0 1)) (uvalueMInt (extract v_5460 1 9)) (uvalueMInt (extract v_5460 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5468 0 1)) (uvalueMInt (extract v_5468 1 9)) (uvalueMInt (extract v_5468 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5477 0 1)) (uvalueMInt (extract v_5477 1 9)) (uvalueMInt (extract v_5477 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5487 0 1)) (uvalueMInt (extract v_5487 1 9)) (uvalueMInt (extract v_5487 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5495 0 1)) (uvalueMInt (extract v_5495 1 9)) (uvalueMInt (extract v_5495 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5504 0 1)) (uvalueMInt (extract v_5504 1 9)) (uvalueMInt (extract v_5504 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5514 0 1)) (uvalueMInt (extract v_5514 1 9)) (uvalueMInt (extract v_5514 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5522 0 1)) (uvalueMInt (extract v_5522 1 9)) (uvalueMInt (extract v_5522 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5531 0 1)) (uvalueMInt (extract v_5531 1 9)) (uvalueMInt (extract v_5531 9 32)))) 32))))));
      pure ()
    pat_end;
    pattern fun (v_2582 : Mem) (v_2580 : reg (bv 128)) (v_2581 : reg (bv 128)) => do
      v_16089 <- getRegister v_2580;
      v_16090 <- eval (extract v_16089 0 32);
      v_16098 <- evaluateAddress v_2582;
      v_16099 <- load v_16098 16;
      v_16100 <- eval (extract v_16099 0 32);
      v_16109 <- getRegister v_2581;
      v_16110 <- eval (extract v_16109 0 32);
      v_16120 <- eval (extract v_16089 32 64);
      v_16128 <- eval (extract v_16099 32 64);
      v_16137 <- eval (extract v_16109 32 64);
      v_16147 <- eval (extract v_16089 64 96);
      v_16155 <- eval (extract v_16099 64 96);
      v_16164 <- eval (extract v_16109 64 96);
      v_16174 <- eval (extract v_16089 96 128);
      v_16182 <- eval (extract v_16099 96 128);
      v_16191 <- eval (extract v_16109 96 128);
      setRegister (lhs.of_reg v_2581) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16090 0 1)) (uvalueMInt (extract v_16090 1 9)) (uvalueMInt (extract v_16090 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16100 0 1)) (uvalueMInt (extract v_16100 1 9)) (uvalueMInt (extract v_16100 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16110 0 1)) (uvalueMInt (extract v_16110 1 9)) (uvalueMInt (extract v_16110 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16120 0 1)) (uvalueMInt (extract v_16120 1 9)) (uvalueMInt (extract v_16120 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16128 0 1)) (uvalueMInt (extract v_16128 1 9)) (uvalueMInt (extract v_16128 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16137 0 1)) (uvalueMInt (extract v_16137 1 9)) (uvalueMInt (extract v_16137 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16147 0 1)) (uvalueMInt (extract v_16147 1 9)) (uvalueMInt (extract v_16147 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16155 0 1)) (uvalueMInt (extract v_16155 1 9)) (uvalueMInt (extract v_16155 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16164 0 1)) (uvalueMInt (extract v_16164 1 9)) (uvalueMInt (extract v_16164 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16174 0 1)) (uvalueMInt (extract v_16174 1 9)) (uvalueMInt (extract v_16174 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16182 0 1)) (uvalueMInt (extract v_16182 1 9)) (uvalueMInt (extract v_16182 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16191 0 1)) (uvalueMInt (extract v_16191 1 9)) (uvalueMInt (extract v_16191 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2591 : Mem) (v_2592 : reg (bv 256)) (v_2593 : reg (bv 256)) => do
      v_16205 <- getRegister v_2592;
      v_16206 <- eval (extract v_16205 0 32);
      v_16214 <- evaluateAddress v_2591;
      v_16215 <- load v_16214 32;
      v_16216 <- eval (extract v_16215 0 32);
      v_16225 <- getRegister v_2593;
      v_16226 <- eval (extract v_16225 0 32);
      v_16236 <- eval (extract v_16205 32 64);
      v_16244 <- eval (extract v_16215 32 64);
      v_16253 <- eval (extract v_16225 32 64);
      v_16264 <- eval (extract v_16205 64 96);
      v_16272 <- eval (extract v_16215 64 96);
      v_16281 <- eval (extract v_16225 64 96);
      v_16291 <- eval (extract v_16205 96 128);
      v_16299 <- eval (extract v_16215 96 128);
      v_16308 <- eval (extract v_16225 96 128);
      v_16319 <- eval (extract v_16205 128 160);
      v_16327 <- eval (extract v_16215 128 160);
      v_16336 <- eval (extract v_16225 128 160);
      v_16346 <- eval (extract v_16205 160 192);
      v_16354 <- eval (extract v_16215 160 192);
      v_16363 <- eval (extract v_16225 160 192);
      v_16373 <- eval (extract v_16205 192 224);
      v_16381 <- eval (extract v_16215 192 224);
      v_16390 <- eval (extract v_16225 192 224);
      v_16400 <- eval (extract v_16205 224 256);
      v_16408 <- eval (extract v_16215 224 256);
      v_16417 <- eval (extract v_16225 224 256);
      setRegister (lhs.of_reg v_2593) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16206 0 1)) (uvalueMInt (extract v_16206 1 9)) (uvalueMInt (extract v_16206 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16216 0 1)) (uvalueMInt (extract v_16216 1 9)) (uvalueMInt (extract v_16216 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16226 0 1)) (uvalueMInt (extract v_16226 1 9)) (uvalueMInt (extract v_16226 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16236 0 1)) (uvalueMInt (extract v_16236 1 9)) (uvalueMInt (extract v_16236 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16244 0 1)) (uvalueMInt (extract v_16244 1 9)) (uvalueMInt (extract v_16244 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16253 0 1)) (uvalueMInt (extract v_16253 1 9)) (uvalueMInt (extract v_16253 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16264 0 1)) (uvalueMInt (extract v_16264 1 9)) (uvalueMInt (extract v_16264 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16272 0 1)) (uvalueMInt (extract v_16272 1 9)) (uvalueMInt (extract v_16272 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16281 0 1)) (uvalueMInt (extract v_16281 1 9)) (uvalueMInt (extract v_16281 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16291 0 1)) (uvalueMInt (extract v_16291 1 9)) (uvalueMInt (extract v_16291 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16299 0 1)) (uvalueMInt (extract v_16299 1 9)) (uvalueMInt (extract v_16299 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16308 0 1)) (uvalueMInt (extract v_16308 1 9)) (uvalueMInt (extract v_16308 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16319 0 1)) (uvalueMInt (extract v_16319 1 9)) (uvalueMInt (extract v_16319 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16327 0 1)) (uvalueMInt (extract v_16327 1 9)) (uvalueMInt (extract v_16327 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16336 0 1)) (uvalueMInt (extract v_16336 1 9)) (uvalueMInt (extract v_16336 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16346 0 1)) (uvalueMInt (extract v_16346 1 9)) (uvalueMInt (extract v_16346 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16354 0 1)) (uvalueMInt (extract v_16354 1 9)) (uvalueMInt (extract v_16354 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16363 0 1)) (uvalueMInt (extract v_16363 1 9)) (uvalueMInt (extract v_16363 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16373 0 1)) (uvalueMInt (extract v_16373 1 9)) (uvalueMInt (extract v_16373 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16381 0 1)) (uvalueMInt (extract v_16381 1 9)) (uvalueMInt (extract v_16381 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16390 0 1)) (uvalueMInt (extract v_16390 1 9)) (uvalueMInt (extract v_16390 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16400 0 1)) (uvalueMInt (extract v_16400 1 9)) (uvalueMInt (extract v_16400 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16408 0 1)) (uvalueMInt (extract v_16408 1 9)) (uvalueMInt (extract v_16408 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_16417 0 1)) (uvalueMInt (extract v_16417 1 9)) (uvalueMInt (extract v_16417 9 32)))) 32))))));
      pure ()
    pat_end
