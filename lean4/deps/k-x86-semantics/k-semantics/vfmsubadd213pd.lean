def vfmsubadd213pd1 : instruction :=
  definst "vfmsubadd213pd" $ do
    pattern fun (v_3003 : reg (bv 128)) (v_3004 : reg (bv 128)) (v_3005 : reg (bv 128)) => do
      v_9476 <- getRegister v_3004;
      v_9477 <- eval (extract v_9476 0 64);
      v_9485 <- getRegister v_3005;
      v_9486 <- eval (extract v_9485 0 64);
      v_9495 <- getRegister v_3003;
      v_9496 <- eval (extract v_9495 0 64);
      v_9506 <- eval (extract v_9476 64 128);
      v_9514 <- eval (extract v_9485 64 128);
      v_9523 <- eval (extract v_9495 64 128);
      setRegister (lhs.of_reg v_3005) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9477 0 1)) (uvalueMInt (extract v_9477 1 12)) (uvalueMInt (extract v_9477 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9486 0 1)) (uvalueMInt (extract v_9486 1 12)) (uvalueMInt (extract v_9486 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9496 0 1)) (uvalueMInt (extract v_9496 1 12)) (uvalueMInt (extract v_9496 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9506 0 1)) (uvalueMInt (extract v_9506 1 12)) (uvalueMInt (extract v_9506 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9514 0 1)) (uvalueMInt (extract v_9514 1 12)) (uvalueMInt (extract v_9514 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9523 0 1)) (uvalueMInt (extract v_9523 1 12)) (uvalueMInt (extract v_9523 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3014 : reg (bv 256)) (v_3015 : reg (bv 256)) (v_3016 : reg (bv 256)) => do
      v_9540 <- getRegister v_3015;
      v_9541 <- eval (extract v_9540 0 64);
      v_9549 <- getRegister v_3016;
      v_9550 <- eval (extract v_9549 0 64);
      v_9559 <- getRegister v_3014;
      v_9560 <- eval (extract v_9559 0 64);
      v_9570 <- eval (extract v_9540 64 128);
      v_9578 <- eval (extract v_9549 64 128);
      v_9587 <- eval (extract v_9559 64 128);
      v_9598 <- eval (extract v_9540 128 192);
      v_9606 <- eval (extract v_9549 128 192);
      v_9615 <- eval (extract v_9559 128 192);
      v_9625 <- eval (extract v_9540 192 256);
      v_9633 <- eval (extract v_9549 192 256);
      v_9642 <- eval (extract v_9559 192 256);
      setRegister (lhs.of_reg v_3016) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9541 0 1)) (uvalueMInt (extract v_9541 1 12)) (uvalueMInt (extract v_9541 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9550 0 1)) (uvalueMInt (extract v_9550 1 12)) (uvalueMInt (extract v_9550 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9560 0 1)) (uvalueMInt (extract v_9560 1 12)) (uvalueMInt (extract v_9560 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9570 0 1)) (uvalueMInt (extract v_9570 1 12)) (uvalueMInt (extract v_9570 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9578 0 1)) (uvalueMInt (extract v_9578 1 12)) (uvalueMInt (extract v_9578 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9587 0 1)) (uvalueMInt (extract v_9587 1 12)) (uvalueMInt (extract v_9587 12 64)))) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9598 0 1)) (uvalueMInt (extract v_9598 1 12)) (uvalueMInt (extract v_9598 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9606 0 1)) (uvalueMInt (extract v_9606 1 12)) (uvalueMInt (extract v_9606 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9615 0 1)) (uvalueMInt (extract v_9615 1 12)) (uvalueMInt (extract v_9615 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9625 0 1)) (uvalueMInt (extract v_9625 1 12)) (uvalueMInt (extract v_9625 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9633 0 1)) (uvalueMInt (extract v_9633 1 12)) (uvalueMInt (extract v_9633 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_9642 0 1)) (uvalueMInt (extract v_9642 1 12)) (uvalueMInt (extract v_9642 12 64)))) 64)));
      pure ()
    pat_end;
    pattern fun (v_3000 : Mem) (v_2998 : reg (bv 128)) (v_2999 : reg (bv 128)) => do
      v_20205 <- getRegister v_2998;
      v_20206 <- eval (extract v_20205 0 64);
      v_20214 <- getRegister v_2999;
      v_20215 <- eval (extract v_20214 0 64);
      v_20224 <- evaluateAddress v_3000;
      v_20225 <- load v_20224 16;
      v_20226 <- eval (extract v_20225 0 64);
      v_20236 <- eval (extract v_20205 64 128);
      v_20244 <- eval (extract v_20214 64 128);
      v_20253 <- eval (extract v_20225 64 128);
      setRegister (lhs.of_reg v_2999) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20206 0 1)) (uvalueMInt (extract v_20206 1 12)) (uvalueMInt (extract v_20206 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20215 0 1)) (uvalueMInt (extract v_20215 1 12)) (uvalueMInt (extract v_20215 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20226 0 1)) (uvalueMInt (extract v_20226 1 12)) (uvalueMInt (extract v_20226 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20236 0 1)) (uvalueMInt (extract v_20236 1 12)) (uvalueMInt (extract v_20236 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20244 0 1)) (uvalueMInt (extract v_20244 1 12)) (uvalueMInt (extract v_20244 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20253 0 1)) (uvalueMInt (extract v_20253 1 12)) (uvalueMInt (extract v_20253 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_3009 : Mem) (v_3010 : reg (bv 256)) (v_3011 : reg (bv 256)) => do
      v_20265 <- getRegister v_3010;
      v_20266 <- eval (extract v_20265 0 64);
      v_20274 <- getRegister v_3011;
      v_20275 <- eval (extract v_20274 0 64);
      v_20284 <- evaluateAddress v_3009;
      v_20285 <- load v_20284 32;
      v_20286 <- eval (extract v_20285 0 64);
      v_20296 <- eval (extract v_20265 64 128);
      v_20304 <- eval (extract v_20274 64 128);
      v_20313 <- eval (extract v_20285 64 128);
      v_20324 <- eval (extract v_20265 128 192);
      v_20332 <- eval (extract v_20274 128 192);
      v_20341 <- eval (extract v_20285 128 192);
      v_20351 <- eval (extract v_20265 192 256);
      v_20359 <- eval (extract v_20274 192 256);
      v_20368 <- eval (extract v_20285 192 256);
      setRegister (lhs.of_reg v_3011) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20266 0 1)) (uvalueMInt (extract v_20266 1 12)) (uvalueMInt (extract v_20266 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20275 0 1)) (uvalueMInt (extract v_20275 1 12)) (uvalueMInt (extract v_20275 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20286 0 1)) (uvalueMInt (extract v_20286 1 12)) (uvalueMInt (extract v_20286 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20296 0 1)) (uvalueMInt (extract v_20296 1 12)) (uvalueMInt (extract v_20296 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20304 0 1)) (uvalueMInt (extract v_20304 1 12)) (uvalueMInt (extract v_20304 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20313 0 1)) (uvalueMInt (extract v_20313 1 12)) (uvalueMInt (extract v_20313 12 64)))) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20324 0 1)) (uvalueMInt (extract v_20324 1 12)) (uvalueMInt (extract v_20324 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20332 0 1)) (uvalueMInt (extract v_20332 1 12)) (uvalueMInt (extract v_20332 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20341 0 1)) (uvalueMInt (extract v_20341 1 12)) (uvalueMInt (extract v_20341 12 64)))) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20351 0 1)) (uvalueMInt (extract v_20351 1 12)) (uvalueMInt (extract v_20351 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20359 0 1)) (uvalueMInt (extract v_20359 1 12)) (uvalueMInt (extract v_20359 12 64)))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_20368 0 1)) (uvalueMInt (extract v_20368 1 12)) (uvalueMInt (extract v_20368 12 64)))) 64)));
      pure ()
    pat_end
