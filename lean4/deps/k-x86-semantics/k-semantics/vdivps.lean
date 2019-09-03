def vdivps1 : instruction :=
  definst "vdivps" $ do
    pattern fun (v_3382 : reg (bv 128)) (v_3383 : reg (bv 128)) (v_3384 : reg (bv 128)) => do
      v_7242 <- getRegister v_3383;
      v_7243 <- eval (extract v_7242 0 32);
      v_7251 <- getRegister v_3382;
      v_7252 <- eval (extract v_7251 0 32);
      v_7262 <- eval (extract v_7242 32 64);
      v_7270 <- eval (extract v_7251 32 64);
      v_7280 <- eval (extract v_7242 64 96);
      v_7288 <- eval (extract v_7251 64 96);
      v_7298 <- eval (extract v_7242 96 128);
      v_7306 <- eval (extract v_7251 96 128);
      setRegister (lhs.of_reg v_3384) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7243 0 1)) (uvalueMInt (extract v_7243 1 9)) (uvalueMInt (extract v_7243 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7252 0 1)) (uvalueMInt (extract v_7252 1 9)) (uvalueMInt (extract v_7252 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7262 0 1)) (uvalueMInt (extract v_7262 1 9)) (uvalueMInt (extract v_7262 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7270 0 1)) (uvalueMInt (extract v_7270 1 9)) (uvalueMInt (extract v_7270 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7280 0 1)) (uvalueMInt (extract v_7280 1 9)) (uvalueMInt (extract v_7280 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7288 0 1)) (uvalueMInt (extract v_7288 1 9)) (uvalueMInt (extract v_7288 9 32)))) 32) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7298 0 1)) (uvalueMInt (extract v_7298 1 9)) (uvalueMInt (extract v_7298 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7306 0 1)) (uvalueMInt (extract v_7306 1 9)) (uvalueMInt (extract v_7306 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3390 : reg (bv 256)) (v_3391 : reg (bv 256)) (v_3392 : reg (bv 256)) => do
      v_7325 <- getRegister v_3391;
      v_7326 <- eval (extract v_7325 0 32);
      v_7334 <- getRegister v_3390;
      v_7335 <- eval (extract v_7334 0 32);
      v_7345 <- eval (extract v_7325 32 64);
      v_7353 <- eval (extract v_7334 32 64);
      v_7363 <- eval (extract v_7325 64 96);
      v_7371 <- eval (extract v_7334 64 96);
      v_7381 <- eval (extract v_7325 96 128);
      v_7389 <- eval (extract v_7334 96 128);
      v_7399 <- eval (extract v_7325 128 160);
      v_7407 <- eval (extract v_7334 128 160);
      v_7417 <- eval (extract v_7325 160 192);
      v_7425 <- eval (extract v_7334 160 192);
      v_7435 <- eval (extract v_7325 192 224);
      v_7443 <- eval (extract v_7334 192 224);
      v_7453 <- eval (extract v_7325 224 256);
      v_7461 <- eval (extract v_7334 224 256);
      setRegister (lhs.of_reg v_3392) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7326 0 1)) (uvalueMInt (extract v_7326 1 9)) (uvalueMInt (extract v_7326 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7335 0 1)) (uvalueMInt (extract v_7335 1 9)) (uvalueMInt (extract v_7335 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7345 0 1)) (uvalueMInt (extract v_7345 1 9)) (uvalueMInt (extract v_7345 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7353 0 1)) (uvalueMInt (extract v_7353 1 9)) (uvalueMInt (extract v_7353 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7363 0 1)) (uvalueMInt (extract v_7363 1 9)) (uvalueMInt (extract v_7363 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7371 0 1)) (uvalueMInt (extract v_7371 1 9)) (uvalueMInt (extract v_7371 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7381 0 1)) (uvalueMInt (extract v_7381 1 9)) (uvalueMInt (extract v_7381 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7389 0 1)) (uvalueMInt (extract v_7389 1 9)) (uvalueMInt (extract v_7389 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7399 0 1)) (uvalueMInt (extract v_7399 1 9)) (uvalueMInt (extract v_7399 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7407 0 1)) (uvalueMInt (extract v_7407 1 9)) (uvalueMInt (extract v_7407 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7417 0 1)) (uvalueMInt (extract v_7417 1 9)) (uvalueMInt (extract v_7417 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7425 0 1)) (uvalueMInt (extract v_7425 1 9)) (uvalueMInt (extract v_7425 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7435 0 1)) (uvalueMInt (extract v_7435 1 9)) (uvalueMInt (extract v_7435 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7443 0 1)) (uvalueMInt (extract v_7443 1 9)) (uvalueMInt (extract v_7443 9 32)))) 32) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7453 0 1)) (uvalueMInt (extract v_7453 1 9)) (uvalueMInt (extract v_7453 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7461 0 1)) (uvalueMInt (extract v_7461 1 9)) (uvalueMInt (extract v_7461 9 32)))) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3374 : Mem) (v_3377 : reg (bv 128)) (v_3378 : reg (bv 128)) => do
      v_12453 <- getRegister v_3377;
      v_12454 <- eval (extract v_12453 0 32);
      v_12462 <- evaluateAddress v_3374;
      v_12463 <- load v_12462 16;
      v_12464 <- eval (extract v_12463 0 32);
      v_12474 <- eval (extract v_12453 32 64);
      v_12482 <- eval (extract v_12463 32 64);
      v_12492 <- eval (extract v_12453 64 96);
      v_12500 <- eval (extract v_12463 64 96);
      v_12510 <- eval (extract v_12453 96 128);
      v_12518 <- eval (extract v_12463 96 128);
      setRegister (lhs.of_reg v_3378) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12454 0 1)) (uvalueMInt (extract v_12454 1 9)) (uvalueMInt (extract v_12454 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12464 0 1)) (uvalueMInt (extract v_12464 1 9)) (uvalueMInt (extract v_12464 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12474 0 1)) (uvalueMInt (extract v_12474 1 9)) (uvalueMInt (extract v_12474 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12482 0 1)) (uvalueMInt (extract v_12482 1 9)) (uvalueMInt (extract v_12482 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12492 0 1)) (uvalueMInt (extract v_12492 1 9)) (uvalueMInt (extract v_12492 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12500 0 1)) (uvalueMInt (extract v_12500 1 9)) (uvalueMInt (extract v_12500 9 32)))) 32) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12510 0 1)) (uvalueMInt (extract v_12510 1 9)) (uvalueMInt (extract v_12510 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12518 0 1)) (uvalueMInt (extract v_12518 1 9)) (uvalueMInt (extract v_12518 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_3385 : Mem) (v_3386 : reg (bv 256)) (v_3387 : reg (bv 256)) => do
      v_12532 <- getRegister v_3386;
      v_12533 <- eval (extract v_12532 0 32);
      v_12541 <- evaluateAddress v_3385;
      v_12542 <- load v_12541 32;
      v_12543 <- eval (extract v_12542 0 32);
      v_12553 <- eval (extract v_12532 32 64);
      v_12561 <- eval (extract v_12542 32 64);
      v_12571 <- eval (extract v_12532 64 96);
      v_12579 <- eval (extract v_12542 64 96);
      v_12589 <- eval (extract v_12532 96 128);
      v_12597 <- eval (extract v_12542 96 128);
      v_12607 <- eval (extract v_12532 128 160);
      v_12615 <- eval (extract v_12542 128 160);
      v_12625 <- eval (extract v_12532 160 192);
      v_12633 <- eval (extract v_12542 160 192);
      v_12643 <- eval (extract v_12532 192 224);
      v_12651 <- eval (extract v_12542 192 224);
      v_12661 <- eval (extract v_12532 224 256);
      v_12669 <- eval (extract v_12542 224 256);
      setRegister (lhs.of_reg v_3387) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12533 0 1)) (uvalueMInt (extract v_12533 1 9)) (uvalueMInt (extract v_12533 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12543 0 1)) (uvalueMInt (extract v_12543 1 9)) (uvalueMInt (extract v_12543 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12553 0 1)) (uvalueMInt (extract v_12553 1 9)) (uvalueMInt (extract v_12553 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12561 0 1)) (uvalueMInt (extract v_12561 1 9)) (uvalueMInt (extract v_12561 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12571 0 1)) (uvalueMInt (extract v_12571 1 9)) (uvalueMInt (extract v_12571 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12579 0 1)) (uvalueMInt (extract v_12579 1 9)) (uvalueMInt (extract v_12579 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12589 0 1)) (uvalueMInt (extract v_12589 1 9)) (uvalueMInt (extract v_12589 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12597 0 1)) (uvalueMInt (extract v_12597 1 9)) (uvalueMInt (extract v_12597 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12607 0 1)) (uvalueMInt (extract v_12607 1 9)) (uvalueMInt (extract v_12607 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12615 0 1)) (uvalueMInt (extract v_12615 1 9)) (uvalueMInt (extract v_12615 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12625 0 1)) (uvalueMInt (extract v_12625 1 9)) (uvalueMInt (extract v_12625 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12633 0 1)) (uvalueMInt (extract v_12633 1 9)) (uvalueMInt (extract v_12633 9 32)))) 32) (concat (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12643 0 1)) (uvalueMInt (extract v_12643 1 9)) (uvalueMInt (extract v_12643 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12651 0 1)) (uvalueMInt (extract v_12651 1 9)) (uvalueMInt (extract v_12651 9 32)))) 32) (Float2MInt (_/Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12661 0 1)) (uvalueMInt (extract v_12661 1 9)) (uvalueMInt (extract v_12661 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12669 0 1)) (uvalueMInt (extract v_12669 1 9)) (uvalueMInt (extract v_12669 9 32)))) 32))))))));
      pure ()
    pat_end
