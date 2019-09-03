def vhsubpd1 : instruction :=
  definst "vhsubpd" $ do
    pattern fun (v_2420 : reg (bv 128)) (v_2421 : reg (bv 128)) (v_2422 : reg (bv 128)) => do
      v_4186 <- getRegister v_2420;
      v_4187 <- eval (extract v_4186 64 128);
      v_4195 <- eval (extract v_4186 0 64);
      v_4205 <- getRegister v_2421;
      v_4206 <- eval (extract v_4205 64 128);
      v_4214 <- eval (extract v_4205 0 64);
      setRegister (lhs.of_reg v_2422) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4187 0 1)) (uvalueMInt (extract v_4187 1 12)) (uvalueMInt (extract v_4187 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4195 0 1)) (uvalueMInt (extract v_4195 1 12)) (uvalueMInt (extract v_4195 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4206 0 1)) (uvalueMInt (extract v_4206 1 12)) (uvalueMInt (extract v_4206 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4214 0 1)) (uvalueMInt (extract v_4214 1 12)) (uvalueMInt (extract v_4214 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2431 : reg (bv 256)) (v_2432 : reg (bv 256)) (v_2433 : reg (bv 256)) => do
      v_4231 <- getRegister v_2431;
      v_4232 <- eval (extract v_4231 64 128);
      v_4240 <- eval (extract v_4231 0 64);
      v_4250 <- getRegister v_2432;
      v_4251 <- eval (extract v_4250 64 128);
      v_4259 <- eval (extract v_4250 0 64);
      v_4270 <- eval (extract v_4231 192 256);
      v_4278 <- eval (extract v_4231 128 192);
      v_4288 <- eval (extract v_4250 192 256);
      v_4296 <- eval (extract v_4250 128 192);
      setRegister (lhs.of_reg v_2433) (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4232 0 1)) (uvalueMInt (extract v_4232 1 12)) (uvalueMInt (extract v_4232 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4240 0 1)) (uvalueMInt (extract v_4240 1 12)) (uvalueMInt (extract v_4240 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4251 0 1)) (uvalueMInt (extract v_4251 1 12)) (uvalueMInt (extract v_4251 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4259 0 1)) (uvalueMInt (extract v_4259 1 12)) (uvalueMInt (extract v_4259 12 64)))) 64)) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4270 0 1)) (uvalueMInt (extract v_4270 1 12)) (uvalueMInt (extract v_4270 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4278 0 1)) (uvalueMInt (extract v_4278 1 12)) (uvalueMInt (extract v_4278 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4288 0 1)) (uvalueMInt (extract v_4288 1 12)) (uvalueMInt (extract v_4288 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4296 0 1)) (uvalueMInt (extract v_4296 1 12)) (uvalueMInt (extract v_4296 12 64)))) 64)));
      pure ()
    pat_end;
    pattern fun (v_2415 : Mem) (v_2416 : reg (bv 128)) (v_2417 : reg (bv 128)) => do
      v_10256 <- evaluateAddress v_2415;
      v_10257 <- load v_10256 16;
      v_10258 <- eval (extract v_10257 64 128);
      v_10266 <- eval (extract v_10257 0 64);
      v_10276 <- getRegister v_2416;
      v_10277 <- eval (extract v_10276 64 128);
      v_10285 <- eval (extract v_10276 0 64);
      setRegister (lhs.of_reg v_2417) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10258 0 1)) (uvalueMInt (extract v_10258 1 12)) (uvalueMInt (extract v_10258 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10266 0 1)) (uvalueMInt (extract v_10266 1 12)) (uvalueMInt (extract v_10266 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10277 0 1)) (uvalueMInt (extract v_10277 1 12)) (uvalueMInt (extract v_10277 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10285 0 1)) (uvalueMInt (extract v_10285 1 12)) (uvalueMInt (extract v_10285 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2426 : Mem) (v_2427 : reg (bv 256)) (v_2428 : reg (bv 256)) => do
      v_10297 <- evaluateAddress v_2426;
      v_10298 <- load v_10297 32;
      v_10299 <- eval (extract v_10298 64 128);
      v_10307 <- eval (extract v_10298 0 64);
      v_10317 <- getRegister v_2427;
      v_10318 <- eval (extract v_10317 64 128);
      v_10326 <- eval (extract v_10317 0 64);
      v_10337 <- eval (extract v_10298 192 256);
      v_10345 <- eval (extract v_10298 128 192);
      v_10355 <- eval (extract v_10317 192 256);
      v_10363 <- eval (extract v_10317 128 192);
      setRegister (lhs.of_reg v_2428) (concat (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10299 0 1)) (uvalueMInt (extract v_10299 1 12)) (uvalueMInt (extract v_10299 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10307 0 1)) (uvalueMInt (extract v_10307 1 12)) (uvalueMInt (extract v_10307 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10318 0 1)) (uvalueMInt (extract v_10318 1 12)) (uvalueMInt (extract v_10318 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10326 0 1)) (uvalueMInt (extract v_10326 1 12)) (uvalueMInt (extract v_10326 12 64)))) 64)) (concat (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10337 0 1)) (uvalueMInt (extract v_10337 1 12)) (uvalueMInt (extract v_10337 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10345 0 1)) (uvalueMInt (extract v_10345 1 12)) (uvalueMInt (extract v_10345 12 64)))) 64) (Float2MInt (_-Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10355 0 1)) (uvalueMInt (extract v_10355 1 12)) (uvalueMInt (extract v_10355 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_10363 0 1)) (uvalueMInt (extract v_10363 1 12)) (uvalueMInt (extract v_10363 12 64)))) 64)));
      pure ()
    pat_end
