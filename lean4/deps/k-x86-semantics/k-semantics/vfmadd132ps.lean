def vfmadd132ps1 : instruction :=
  definst "vfmadd132ps" $ do
    pattern fun (v_2453 : reg (bv 128)) (v_2454 : reg (bv 128)) (v_2455 : reg (bv 128)) => do
      v_4151 <- getRegister v_2455;
      v_4152 <- eval (extract v_4151 0 32);
      v_4160 <- getRegister v_2453;
      v_4161 <- eval (extract v_4160 0 32);
      v_4170 <- getRegister v_2454;
      v_4171 <- eval (extract v_4170 0 32);
      v_4181 <- eval (extract v_4151 32 64);
      v_4189 <- eval (extract v_4160 32 64);
      v_4198 <- eval (extract v_4170 32 64);
      v_4208 <- eval (extract v_4151 64 96);
      v_4216 <- eval (extract v_4160 64 96);
      v_4225 <- eval (extract v_4170 64 96);
      v_4235 <- eval (extract v_4151 96 128);
      v_4243 <- eval (extract v_4160 96 128);
      v_4252 <- eval (extract v_4170 96 128);
      setRegister (lhs.of_reg v_2455) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4152 0 1)) (uvalueMInt (extract v_4152 1 9)) (uvalueMInt (extract v_4152 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4161 0 1)) (uvalueMInt (extract v_4161 1 9)) (uvalueMInt (extract v_4161 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4171 0 1)) (uvalueMInt (extract v_4171 1 9)) (uvalueMInt (extract v_4171 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4181 0 1)) (uvalueMInt (extract v_4181 1 9)) (uvalueMInt (extract v_4181 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4189 0 1)) (uvalueMInt (extract v_4189 1 9)) (uvalueMInt (extract v_4189 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4198 0 1)) (uvalueMInt (extract v_4198 1 9)) (uvalueMInt (extract v_4198 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4208 0 1)) (uvalueMInt (extract v_4208 1 9)) (uvalueMInt (extract v_4208 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4216 0 1)) (uvalueMInt (extract v_4216 1 9)) (uvalueMInt (extract v_4216 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4225 0 1)) (uvalueMInt (extract v_4225 1 9)) (uvalueMInt (extract v_4225 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4235 0 1)) (uvalueMInt (extract v_4235 1 9)) (uvalueMInt (extract v_4235 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4243 0 1)) (uvalueMInt (extract v_4243 1 9)) (uvalueMInt (extract v_4243 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4252 0 1)) (uvalueMInt (extract v_4252 1 9)) (uvalueMInt (extract v_4252 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2464 : reg (bv 256)) (v_2465 : reg (bv 256)) (v_2466 : reg (bv 256)) => do
      v_4271 <- getRegister v_2466;
      v_4272 <- eval (extract v_4271 0 32);
      v_4280 <- getRegister v_2464;
      v_4281 <- eval (extract v_4280 0 32);
      v_4290 <- getRegister v_2465;
      v_4291 <- eval (extract v_4290 0 32);
      v_4301 <- eval (extract v_4271 32 64);
      v_4309 <- eval (extract v_4280 32 64);
      v_4318 <- eval (extract v_4290 32 64);
      v_4328 <- eval (extract v_4271 64 96);
      v_4336 <- eval (extract v_4280 64 96);
      v_4345 <- eval (extract v_4290 64 96);
      v_4355 <- eval (extract v_4271 96 128);
      v_4363 <- eval (extract v_4280 96 128);
      v_4372 <- eval (extract v_4290 96 128);
      v_4382 <- eval (extract v_4271 128 160);
      v_4390 <- eval (extract v_4280 128 160);
      v_4399 <- eval (extract v_4290 128 160);
      v_4409 <- eval (extract v_4271 160 192);
      v_4417 <- eval (extract v_4280 160 192);
      v_4426 <- eval (extract v_4290 160 192);
      v_4436 <- eval (extract v_4271 192 224);
      v_4444 <- eval (extract v_4280 192 224);
      v_4453 <- eval (extract v_4290 192 224);
      v_4463 <- eval (extract v_4271 224 256);
      v_4471 <- eval (extract v_4280 224 256);
      v_4480 <- eval (extract v_4290 224 256);
      setRegister (lhs.of_reg v_2466) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4272 0 1)) (uvalueMInt (extract v_4272 1 9)) (uvalueMInt (extract v_4272 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4281 0 1)) (uvalueMInt (extract v_4281 1 9)) (uvalueMInt (extract v_4281 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4291 0 1)) (uvalueMInt (extract v_4291 1 9)) (uvalueMInt (extract v_4291 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4301 0 1)) (uvalueMInt (extract v_4301 1 9)) (uvalueMInt (extract v_4301 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4309 0 1)) (uvalueMInt (extract v_4309 1 9)) (uvalueMInt (extract v_4309 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4318 0 1)) (uvalueMInt (extract v_4318 1 9)) (uvalueMInt (extract v_4318 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4328 0 1)) (uvalueMInt (extract v_4328 1 9)) (uvalueMInt (extract v_4328 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4336 0 1)) (uvalueMInt (extract v_4336 1 9)) (uvalueMInt (extract v_4336 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4345 0 1)) (uvalueMInt (extract v_4345 1 9)) (uvalueMInt (extract v_4345 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4355 0 1)) (uvalueMInt (extract v_4355 1 9)) (uvalueMInt (extract v_4355 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4363 0 1)) (uvalueMInt (extract v_4363 1 9)) (uvalueMInt (extract v_4363 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4372 0 1)) (uvalueMInt (extract v_4372 1 9)) (uvalueMInt (extract v_4372 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4382 0 1)) (uvalueMInt (extract v_4382 1 9)) (uvalueMInt (extract v_4382 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4390 0 1)) (uvalueMInt (extract v_4390 1 9)) (uvalueMInt (extract v_4390 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4399 0 1)) (uvalueMInt (extract v_4399 1 9)) (uvalueMInt (extract v_4399 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4409 0 1)) (uvalueMInt (extract v_4409 1 9)) (uvalueMInt (extract v_4409 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4417 0 1)) (uvalueMInt (extract v_4417 1 9)) (uvalueMInt (extract v_4417 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4426 0 1)) (uvalueMInt (extract v_4426 1 9)) (uvalueMInt (extract v_4426 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4436 0 1)) (uvalueMInt (extract v_4436 1 9)) (uvalueMInt (extract v_4436 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4444 0 1)) (uvalueMInt (extract v_4444 1 9)) (uvalueMInt (extract v_4444 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4453 0 1)) (uvalueMInt (extract v_4453 1 9)) (uvalueMInt (extract v_4453 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4463 0 1)) (uvalueMInt (extract v_4463 1 9)) (uvalueMInt (extract v_4463 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4471 0 1)) (uvalueMInt (extract v_4471 1 9)) (uvalueMInt (extract v_4471 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4480 0 1)) (uvalueMInt (extract v_4480 1 9)) (uvalueMInt (extract v_4480 9 32)))) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2450 : Mem) (v_2448 : reg (bv 128)) (v_2449 : reg (bv 128)) => do
      v_15092 <- getRegister v_2449;
      v_15093 <- eval (extract v_15092 0 32);
      v_15101 <- evaluateAddress v_2450;
      v_15102 <- load v_15101 16;
      v_15103 <- eval (extract v_15102 0 32);
      v_15112 <- getRegister v_2448;
      v_15113 <- eval (extract v_15112 0 32);
      v_15123 <- eval (extract v_15092 32 64);
      v_15131 <- eval (extract v_15102 32 64);
      v_15140 <- eval (extract v_15112 32 64);
      v_15150 <- eval (extract v_15092 64 96);
      v_15158 <- eval (extract v_15102 64 96);
      v_15167 <- eval (extract v_15112 64 96);
      v_15177 <- eval (extract v_15092 96 128);
      v_15185 <- eval (extract v_15102 96 128);
      v_15194 <- eval (extract v_15112 96 128);
      setRegister (lhs.of_reg v_2449) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15093 0 1)) (uvalueMInt (extract v_15093 1 9)) (uvalueMInt (extract v_15093 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15103 0 1)) (uvalueMInt (extract v_15103 1 9)) (uvalueMInt (extract v_15103 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15113 0 1)) (uvalueMInt (extract v_15113 1 9)) (uvalueMInt (extract v_15113 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15123 0 1)) (uvalueMInt (extract v_15123 1 9)) (uvalueMInt (extract v_15123 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15131 0 1)) (uvalueMInt (extract v_15131 1 9)) (uvalueMInt (extract v_15131 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15140 0 1)) (uvalueMInt (extract v_15140 1 9)) (uvalueMInt (extract v_15140 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15150 0 1)) (uvalueMInt (extract v_15150 1 9)) (uvalueMInt (extract v_15150 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15158 0 1)) (uvalueMInt (extract v_15158 1 9)) (uvalueMInt (extract v_15158 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15167 0 1)) (uvalueMInt (extract v_15167 1 9)) (uvalueMInt (extract v_15167 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15177 0 1)) (uvalueMInt (extract v_15177 1 9)) (uvalueMInt (extract v_15177 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15185 0 1)) (uvalueMInt (extract v_15185 1 9)) (uvalueMInt (extract v_15185 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15194 0 1)) (uvalueMInt (extract v_15194 1 9)) (uvalueMInt (extract v_15194 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2459 : Mem) (v_2460 : reg (bv 256)) (v_2461 : reg (bv 256)) => do
      v_15208 <- getRegister v_2461;
      v_15209 <- eval (extract v_15208 0 32);
      v_15217 <- evaluateAddress v_2459;
      v_15218 <- load v_15217 32;
      v_15219 <- eval (extract v_15218 0 32);
      v_15228 <- getRegister v_2460;
      v_15229 <- eval (extract v_15228 0 32);
      v_15239 <- eval (extract v_15208 32 64);
      v_15247 <- eval (extract v_15218 32 64);
      v_15256 <- eval (extract v_15228 32 64);
      v_15266 <- eval (extract v_15208 64 96);
      v_15274 <- eval (extract v_15218 64 96);
      v_15283 <- eval (extract v_15228 64 96);
      v_15293 <- eval (extract v_15208 96 128);
      v_15301 <- eval (extract v_15218 96 128);
      v_15310 <- eval (extract v_15228 96 128);
      v_15320 <- eval (extract v_15208 128 160);
      v_15328 <- eval (extract v_15218 128 160);
      v_15337 <- eval (extract v_15228 128 160);
      v_15347 <- eval (extract v_15208 160 192);
      v_15355 <- eval (extract v_15218 160 192);
      v_15364 <- eval (extract v_15228 160 192);
      v_15374 <- eval (extract v_15208 192 224);
      v_15382 <- eval (extract v_15218 192 224);
      v_15391 <- eval (extract v_15228 192 224);
      v_15401 <- eval (extract v_15208 224 256);
      v_15409 <- eval (extract v_15218 224 256);
      v_15418 <- eval (extract v_15228 224 256);
      setRegister (lhs.of_reg v_2461) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15209 0 1)) (uvalueMInt (extract v_15209 1 9)) (uvalueMInt (extract v_15209 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15219 0 1)) (uvalueMInt (extract v_15219 1 9)) (uvalueMInt (extract v_15219 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15229 0 1)) (uvalueMInt (extract v_15229 1 9)) (uvalueMInt (extract v_15229 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15239 0 1)) (uvalueMInt (extract v_15239 1 9)) (uvalueMInt (extract v_15239 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15247 0 1)) (uvalueMInt (extract v_15247 1 9)) (uvalueMInt (extract v_15247 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15256 0 1)) (uvalueMInt (extract v_15256 1 9)) (uvalueMInt (extract v_15256 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15266 0 1)) (uvalueMInt (extract v_15266 1 9)) (uvalueMInt (extract v_15266 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15274 0 1)) (uvalueMInt (extract v_15274 1 9)) (uvalueMInt (extract v_15274 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15283 0 1)) (uvalueMInt (extract v_15283 1 9)) (uvalueMInt (extract v_15283 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15293 0 1)) (uvalueMInt (extract v_15293 1 9)) (uvalueMInt (extract v_15293 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15301 0 1)) (uvalueMInt (extract v_15301 1 9)) (uvalueMInt (extract v_15301 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15310 0 1)) (uvalueMInt (extract v_15310 1 9)) (uvalueMInt (extract v_15310 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15320 0 1)) (uvalueMInt (extract v_15320 1 9)) (uvalueMInt (extract v_15320 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15328 0 1)) (uvalueMInt (extract v_15328 1 9)) (uvalueMInt (extract v_15328 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15337 0 1)) (uvalueMInt (extract v_15337 1 9)) (uvalueMInt (extract v_15337 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15347 0 1)) (uvalueMInt (extract v_15347 1 9)) (uvalueMInt (extract v_15347 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15355 0 1)) (uvalueMInt (extract v_15355 1 9)) (uvalueMInt (extract v_15355 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15364 0 1)) (uvalueMInt (extract v_15364 1 9)) (uvalueMInt (extract v_15364 9 32)))) 32) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15374 0 1)) (uvalueMInt (extract v_15374 1 9)) (uvalueMInt (extract v_15374 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15382 0 1)) (uvalueMInt (extract v_15382 1 9)) (uvalueMInt (extract v_15382 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15391 0 1)) (uvalueMInt (extract v_15391 1 9)) (uvalueMInt (extract v_15391 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15401 0 1)) (uvalueMInt (extract v_15401 1 9)) (uvalueMInt (extract v_15401 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15409 0 1)) (uvalueMInt (extract v_15409 1 9)) (uvalueMInt (extract v_15409 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_15418 0 1)) (uvalueMInt (extract v_15418 1 9)) (uvalueMInt (extract v_15418 9 32)))) 32))))))));
      pure ()
    pat_end
