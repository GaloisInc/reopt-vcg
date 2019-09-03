def vmulpd1 : instruction :=
  definst "vmulpd" $ do
    pattern fun (v_3082 : reg (bv 128)) (v_3083 : reg (bv 128)) (v_3084 : reg (bv 128)) => do
      v_5469 <- getRegister v_3083;
      v_5470 <- eval (extract v_5469 0 64);
      v_5478 <- getRegister v_3082;
      v_5479 <- eval (extract v_5478 0 64);
      v_5489 <- eval (extract v_5469 64 128);
      v_5497 <- eval (extract v_5478 64 128);
      setRegister (lhs.of_reg v_3084) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5470 0 1)) (uvalueMInt (extract v_5470 1 12)) (uvalueMInt (extract v_5470 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5479 0 1)) (uvalueMInt (extract v_5479 1 12)) (uvalueMInt (extract v_5479 12 64)))) 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5489 0 1)) (uvalueMInt (extract v_5489 1 12)) (uvalueMInt (extract v_5489 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5497 0 1)) (uvalueMInt (extract v_5497 1 12)) (uvalueMInt (extract v_5497 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3093 : reg (bv 256)) (v_3094 : reg (bv 256)) (v_3095 : reg (bv 256)) => do
      v_5514 <- getRegister v_3094;
      v_5515 <- eval (extract v_5514 0 64);
      v_5523 <- getRegister v_3093;
      v_5524 <- eval (extract v_5523 0 64);
      v_5534 <- eval (extract v_5514 64 128);
      v_5542 <- eval (extract v_5523 64 128);
      v_5552 <- eval (extract v_5514 128 192);
      v_5560 <- eval (extract v_5523 128 192);
      v_5570 <- eval (extract v_5514 192 256);
      v_5578 <- eval (extract v_5523 192 256);
      setRegister (lhs.of_reg v_3095) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5515 0 1)) (uvalueMInt (extract v_5515 1 12)) (uvalueMInt (extract v_5515 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5524 0 1)) (uvalueMInt (extract v_5524 1 12)) (uvalueMInt (extract v_5524 12 64)))) 64) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5534 0 1)) (uvalueMInt (extract v_5534 1 12)) (uvalueMInt (extract v_5534 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5542 0 1)) (uvalueMInt (extract v_5542 1 12)) (uvalueMInt (extract v_5542 12 64)))) 64) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5552 0 1)) (uvalueMInt (extract v_5552 1 12)) (uvalueMInt (extract v_5552 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5560 0 1)) (uvalueMInt (extract v_5560 1 12)) (uvalueMInt (extract v_5560 12 64)))) 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5570 0 1)) (uvalueMInt (extract v_5570 1 12)) (uvalueMInt (extract v_5570 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5578 0 1)) (uvalueMInt (extract v_5578 1 12)) (uvalueMInt (extract v_5578 12 64)))) 64))));
      pure ()
    pat_end;
    pattern fun (v_3077 : Mem) (v_3078 : reg (bv 128)) (v_3079 : reg (bv 128)) => do
      v_11225 <- getRegister v_3078;
      v_11226 <- eval (extract v_11225 0 64);
      v_11234 <- evaluateAddress v_3077;
      v_11235 <- load v_11234 16;
      v_11236 <- eval (extract v_11235 0 64);
      v_11246 <- eval (extract v_11225 64 128);
      v_11254 <- eval (extract v_11235 64 128);
      setRegister (lhs.of_reg v_3079) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11226 0 1)) (uvalueMInt (extract v_11226 1 12)) (uvalueMInt (extract v_11226 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11236 0 1)) (uvalueMInt (extract v_11236 1 12)) (uvalueMInt (extract v_11236 12 64)))) 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11246 0 1)) (uvalueMInt (extract v_11246 1 12)) (uvalueMInt (extract v_11246 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11254 0 1)) (uvalueMInt (extract v_11254 1 12)) (uvalueMInt (extract v_11254 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3088 : Mem) (v_3089 : reg (bv 256)) (v_3090 : reg (bv 256)) => do
      v_11266 <- getRegister v_3089;
      v_11267 <- eval (extract v_11266 0 64);
      v_11275 <- evaluateAddress v_3088;
      v_11276 <- load v_11275 32;
      v_11277 <- eval (extract v_11276 0 64);
      v_11287 <- eval (extract v_11266 64 128);
      v_11295 <- eval (extract v_11276 64 128);
      v_11305 <- eval (extract v_11266 128 192);
      v_11313 <- eval (extract v_11276 128 192);
      v_11323 <- eval (extract v_11266 192 256);
      v_11331 <- eval (extract v_11276 192 256);
      setRegister (lhs.of_reg v_3090) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11267 0 1)) (uvalueMInt (extract v_11267 1 12)) (uvalueMInt (extract v_11267 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11277 0 1)) (uvalueMInt (extract v_11277 1 12)) (uvalueMInt (extract v_11277 12 64)))) 64) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11287 0 1)) (uvalueMInt (extract v_11287 1 12)) (uvalueMInt (extract v_11287 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11295 0 1)) (uvalueMInt (extract v_11295 1 12)) (uvalueMInt (extract v_11295 12 64)))) 64) (concat (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11305 0 1)) (uvalueMInt (extract v_11305 1 12)) (uvalueMInt (extract v_11305 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11313 0 1)) (uvalueMInt (extract v_11313 1 12)) (uvalueMInt (extract v_11313 12 64)))) 64) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11323 0 1)) (uvalueMInt (extract v_11323 1 12)) (uvalueMInt (extract v_11323 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_11331 0 1)) (uvalueMInt (extract v_11331 1 12)) (uvalueMInt (extract v_11331 12 64)))) 64))));
      pure ()
    pat_end
