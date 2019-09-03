def vdivpd1 : instruction :=
  definst "vdivpd" $ do
    pattern fun (v_3360 : reg (bv 128)) (v_3361 : reg (bv 128)) (v_3362 : reg (bv 128)) => do
      v_7114 <- getRegister v_3361;
      v_7115 <- eval (extract v_7114 0 64);
      v_7123 <- getRegister v_3360;
      v_7124 <- eval (extract v_7123 0 64);
      v_7134 <- eval (extract v_7114 64 128);
      v_7142 <- eval (extract v_7123 64 128);
      setRegister (lhs.of_reg v_3362) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7115 0 1)) (uvalueMInt (extract v_7115 1 12)) (uvalueMInt (extract v_7115 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7124 0 1)) (uvalueMInt (extract v_7124 1 12)) (uvalueMInt (extract v_7124 12 64)))) 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7134 0 1)) (uvalueMInt (extract v_7134 1 12)) (uvalueMInt (extract v_7134 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7142 0 1)) (uvalueMInt (extract v_7142 1 12)) (uvalueMInt (extract v_7142 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3368 : reg (bv 256)) (v_3369 : reg (bv 256)) (v_3370 : reg (bv 256)) => do
      v_7159 <- getRegister v_3369;
      v_7160 <- eval (extract v_7159 0 64);
      v_7168 <- getRegister v_3368;
      v_7169 <- eval (extract v_7168 0 64);
      v_7179 <- eval (extract v_7159 64 128);
      v_7187 <- eval (extract v_7168 64 128);
      v_7197 <- eval (extract v_7159 128 192);
      v_7205 <- eval (extract v_7168 128 192);
      v_7215 <- eval (extract v_7159 192 256);
      v_7223 <- eval (extract v_7168 192 256);
      setRegister (lhs.of_reg v_3370) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7160 0 1)) (uvalueMInt (extract v_7160 1 12)) (uvalueMInt (extract v_7160 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7169 0 1)) (uvalueMInt (extract v_7169 1 12)) (uvalueMInt (extract v_7169 12 64)))) 64) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7179 0 1)) (uvalueMInt (extract v_7179 1 12)) (uvalueMInt (extract v_7179 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7187 0 1)) (uvalueMInt (extract v_7187 1 12)) (uvalueMInt (extract v_7187 12 64)))) 64) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7197 0 1)) (uvalueMInt (extract v_7197 1 12)) (uvalueMInt (extract v_7197 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7205 0 1)) (uvalueMInt (extract v_7205 1 12)) (uvalueMInt (extract v_7205 12 64)))) 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7215 0 1)) (uvalueMInt (extract v_7215 1 12)) (uvalueMInt (extract v_7215 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_7223 0 1)) (uvalueMInt (extract v_7223 1 12)) (uvalueMInt (extract v_7223 12 64)))) 64))));
      pure ()
    pat_end;
    pattern fun (v_3352 : Mem) (v_3355 : reg (bv 128)) (v_3356 : reg (bv 128)) => do
      v_12333 <- getRegister v_3355;
      v_12334 <- eval (extract v_12333 0 64);
      v_12342 <- evaluateAddress v_3352;
      v_12343 <- load v_12342 16;
      v_12344 <- eval (extract v_12343 0 64);
      v_12354 <- eval (extract v_12333 64 128);
      v_12362 <- eval (extract v_12343 64 128);
      setRegister (lhs.of_reg v_3356) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12334 0 1)) (uvalueMInt (extract v_12334 1 12)) (uvalueMInt (extract v_12334 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12344 0 1)) (uvalueMInt (extract v_12344 1 12)) (uvalueMInt (extract v_12344 12 64)))) 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12354 0 1)) (uvalueMInt (extract v_12354 1 12)) (uvalueMInt (extract v_12354 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12362 0 1)) (uvalueMInt (extract v_12362 1 12)) (uvalueMInt (extract v_12362 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3363 : Mem) (v_3364 : reg (bv 256)) (v_3365 : reg (bv 256)) => do
      v_12374 <- getRegister v_3364;
      v_12375 <- eval (extract v_12374 0 64);
      v_12383 <- evaluateAddress v_3363;
      v_12384 <- load v_12383 32;
      v_12385 <- eval (extract v_12384 0 64);
      v_12395 <- eval (extract v_12374 64 128);
      v_12403 <- eval (extract v_12384 64 128);
      v_12413 <- eval (extract v_12374 128 192);
      v_12421 <- eval (extract v_12384 128 192);
      v_12431 <- eval (extract v_12374 192 256);
      v_12439 <- eval (extract v_12384 192 256);
      setRegister (lhs.of_reg v_3365) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12375 0 1)) (uvalueMInt (extract v_12375 1 12)) (uvalueMInt (extract v_12375 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12385 0 1)) (uvalueMInt (extract v_12385 1 12)) (uvalueMInt (extract v_12385 12 64)))) 64) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12395 0 1)) (uvalueMInt (extract v_12395 1 12)) (uvalueMInt (extract v_12395 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12403 0 1)) (uvalueMInt (extract v_12403 1 12)) (uvalueMInt (extract v_12403 12 64)))) 64) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12413 0 1)) (uvalueMInt (extract v_12413 1 12)) (uvalueMInt (extract v_12413 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12421 0 1)) (uvalueMInt (extract v_12421 1 12)) (uvalueMInt (extract v_12421 12 64)))) 64) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12431 0 1)) (uvalueMInt (extract v_12431 1 12)) (uvalueMInt (extract v_12431 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12439 0 1)) (uvalueMInt (extract v_12439 1 12)) (uvalueMInt (extract v_12439 12 64)))) 64))));
      pure ()
    pat_end
