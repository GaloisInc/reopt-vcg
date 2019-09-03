def vfmsub132ps1 : instruction :=
  definst "vfmsub132ps" $ do
    pattern fun (v_2783 : reg (bv 128)) (v_2784 : reg (bv 128)) (v_2785 : reg (bv 128)) => do
      v_7354 <- getRegister v_2785;
      v_7355 <- eval (extract v_7354 0 32);
      v_7363 <- getRegister v_2783;
      v_7364 <- eval (extract v_7363 0 32);
      v_7373 <- getRegister v_2784;
      v_7374 <- eval (extract v_7373 0 32);
      v_7384 <- eval (extract v_7354 32 64);
      v_7392 <- eval (extract v_7363 32 64);
      v_7401 <- eval (extract v_7373 32 64);
      v_7411 <- eval (extract v_7354 64 96);
      v_7419 <- eval (extract v_7363 64 96);
      v_7428 <- eval (extract v_7373 64 96);
      v_7438 <- eval (extract v_7354 96 128);
      v_7446 <- eval (extract v_7363 96 128);
      v_7455 <- eval (extract v_7373 96 128);
      setRegister (lhs.of_reg v_2785) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7355 0 1)) (uvalueMInt (extract v_7355 1 9)) (uvalueMInt (extract v_7355 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7364 0 1)) (uvalueMInt (extract v_7364 1 9)) (uvalueMInt (extract v_7364 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7374 0 1)) (uvalueMInt (extract v_7374 1 9)) (uvalueMInt (extract v_7374 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7384 0 1)) (uvalueMInt (extract v_7384 1 9)) (uvalueMInt (extract v_7384 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7392 0 1)) (uvalueMInt (extract v_7392 1 9)) (uvalueMInt (extract v_7392 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7401 0 1)) (uvalueMInt (extract v_7401 1 9)) (uvalueMInt (extract v_7401 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7411 0 1)) (uvalueMInt (extract v_7411 1 9)) (uvalueMInt (extract v_7411 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7419 0 1)) (uvalueMInt (extract v_7419 1 9)) (uvalueMInt (extract v_7419 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7428 0 1)) (uvalueMInt (extract v_7428 1 9)) (uvalueMInt (extract v_7428 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7438 0 1)) (uvalueMInt (extract v_7438 1 9)) (uvalueMInt (extract v_7438 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7446 0 1)) (uvalueMInt (extract v_7446 1 9)) (uvalueMInt (extract v_7446 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7455 0 1)) (uvalueMInt (extract v_7455 1 9)) (uvalueMInt (extract v_7455 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2794 : reg (bv 256)) (v_2795 : reg (bv 256)) (v_2796 : reg (bv 256)) => do
      v_7474 <- getRegister v_2796;
      v_7475 <- eval (extract v_7474 0 32);
      v_7483 <- getRegister v_2794;
      v_7484 <- eval (extract v_7483 0 32);
      v_7493 <- getRegister v_2795;
      v_7494 <- eval (extract v_7493 0 32);
      v_7504 <- eval (extract v_7474 32 64);
      v_7512 <- eval (extract v_7483 32 64);
      v_7521 <- eval (extract v_7493 32 64);
      v_7531 <- eval (extract v_7474 64 96);
      v_7539 <- eval (extract v_7483 64 96);
      v_7548 <- eval (extract v_7493 64 96);
      v_7558 <- eval (extract v_7474 96 128);
      v_7566 <- eval (extract v_7483 96 128);
      v_7575 <- eval (extract v_7493 96 128);
      v_7585 <- eval (extract v_7474 128 160);
      v_7593 <- eval (extract v_7483 128 160);
      v_7602 <- eval (extract v_7493 128 160);
      v_7612 <- eval (extract v_7474 160 192);
      v_7620 <- eval (extract v_7483 160 192);
      v_7629 <- eval (extract v_7493 160 192);
      v_7639 <- eval (extract v_7474 192 224);
      v_7647 <- eval (extract v_7483 192 224);
      v_7656 <- eval (extract v_7493 192 224);
      v_7666 <- eval (extract v_7474 224 256);
      v_7674 <- eval (extract v_7483 224 256);
      v_7683 <- eval (extract v_7493 224 256);
      setRegister (lhs.of_reg v_2796) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7475 0 1)) (uvalueMInt (extract v_7475 1 9)) (uvalueMInt (extract v_7475 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7484 0 1)) (uvalueMInt (extract v_7484 1 9)) (uvalueMInt (extract v_7484 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7494 0 1)) (uvalueMInt (extract v_7494 1 9)) (uvalueMInt (extract v_7494 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7504 0 1)) (uvalueMInt (extract v_7504 1 9)) (uvalueMInt (extract v_7504 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7512 0 1)) (uvalueMInt (extract v_7512 1 9)) (uvalueMInt (extract v_7512 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7521 0 1)) (uvalueMInt (extract v_7521 1 9)) (uvalueMInt (extract v_7521 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7531 0 1)) (uvalueMInt (extract v_7531 1 9)) (uvalueMInt (extract v_7531 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7539 0 1)) (uvalueMInt (extract v_7539 1 9)) (uvalueMInt (extract v_7539 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7548 0 1)) (uvalueMInt (extract v_7548 1 9)) (uvalueMInt (extract v_7548 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7558 0 1)) (uvalueMInt (extract v_7558 1 9)) (uvalueMInt (extract v_7558 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7566 0 1)) (uvalueMInt (extract v_7566 1 9)) (uvalueMInt (extract v_7566 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7575 0 1)) (uvalueMInt (extract v_7575 1 9)) (uvalueMInt (extract v_7575 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7585 0 1)) (uvalueMInt (extract v_7585 1 9)) (uvalueMInt (extract v_7585 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7593 0 1)) (uvalueMInt (extract v_7593 1 9)) (uvalueMInt (extract v_7593 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7602 0 1)) (uvalueMInt (extract v_7602 1 9)) (uvalueMInt (extract v_7602 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7612 0 1)) (uvalueMInt (extract v_7612 1 9)) (uvalueMInt (extract v_7612 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7620 0 1)) (uvalueMInt (extract v_7620 1 9)) (uvalueMInt (extract v_7620 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7629 0 1)) (uvalueMInt (extract v_7629 1 9)) (uvalueMInt (extract v_7629 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7639 0 1)) (uvalueMInt (extract v_7639 1 9)) (uvalueMInt (extract v_7639 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7647 0 1)) (uvalueMInt (extract v_7647 1 9)) (uvalueMInt (extract v_7647 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7656 0 1)) (uvalueMInt (extract v_7656 1 9)) (uvalueMInt (extract v_7656 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7666 0 1)) (uvalueMInt (extract v_7666 1 9)) (uvalueMInt (extract v_7666 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7674 0 1)) (uvalueMInt (extract v_7674 1 9)) (uvalueMInt (extract v_7674 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7683 0 1)) (uvalueMInt (extract v_7683 1 9)) (uvalueMInt (extract v_7683 9 32)))) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2780 : Mem) (v_2778 : reg (bv 128)) (v_2779 : reg (bv 128)) => do
      v_18169 <- getRegister v_2779;
      v_18170 <- eval (extract v_18169 0 32);
      v_18178 <- evaluateAddress v_2780;
      v_18179 <- load v_18178 16;
      v_18180 <- eval (extract v_18179 0 32);
      v_18189 <- getRegister v_2778;
      v_18190 <- eval (extract v_18189 0 32);
      v_18200 <- eval (extract v_18169 32 64);
      v_18208 <- eval (extract v_18179 32 64);
      v_18217 <- eval (extract v_18189 32 64);
      v_18227 <- eval (extract v_18169 64 96);
      v_18235 <- eval (extract v_18179 64 96);
      v_18244 <- eval (extract v_18189 64 96);
      v_18254 <- eval (extract v_18169 96 128);
      v_18262 <- eval (extract v_18179 96 128);
      v_18271 <- eval (extract v_18189 96 128);
      setRegister (lhs.of_reg v_2779) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18170 0 1)) (uvalueMInt (extract v_18170 1 9)) (uvalueMInt (extract v_18170 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18180 0 1)) (uvalueMInt (extract v_18180 1 9)) (uvalueMInt (extract v_18180 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18190 0 1)) (uvalueMInt (extract v_18190 1 9)) (uvalueMInt (extract v_18190 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18200 0 1)) (uvalueMInt (extract v_18200 1 9)) (uvalueMInt (extract v_18200 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18208 0 1)) (uvalueMInt (extract v_18208 1 9)) (uvalueMInt (extract v_18208 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18217 0 1)) (uvalueMInt (extract v_18217 1 9)) (uvalueMInt (extract v_18217 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18227 0 1)) (uvalueMInt (extract v_18227 1 9)) (uvalueMInt (extract v_18227 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18235 0 1)) (uvalueMInt (extract v_18235 1 9)) (uvalueMInt (extract v_18235 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18244 0 1)) (uvalueMInt (extract v_18244 1 9)) (uvalueMInt (extract v_18244 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18254 0 1)) (uvalueMInt (extract v_18254 1 9)) (uvalueMInt (extract v_18254 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18262 0 1)) (uvalueMInt (extract v_18262 1 9)) (uvalueMInt (extract v_18262 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18271 0 1)) (uvalueMInt (extract v_18271 1 9)) (uvalueMInt (extract v_18271 9 32)))) 32))));
      pure ()
    pat_end;
    pattern fun (v_2789 : Mem) (v_2790 : reg (bv 256)) (v_2791 : reg (bv 256)) => do
      v_18285 <- getRegister v_2791;
      v_18286 <- eval (extract v_18285 0 32);
      v_18294 <- evaluateAddress v_2789;
      v_18295 <- load v_18294 32;
      v_18296 <- eval (extract v_18295 0 32);
      v_18305 <- getRegister v_2790;
      v_18306 <- eval (extract v_18305 0 32);
      v_18316 <- eval (extract v_18285 32 64);
      v_18324 <- eval (extract v_18295 32 64);
      v_18333 <- eval (extract v_18305 32 64);
      v_18343 <- eval (extract v_18285 64 96);
      v_18351 <- eval (extract v_18295 64 96);
      v_18360 <- eval (extract v_18305 64 96);
      v_18370 <- eval (extract v_18285 96 128);
      v_18378 <- eval (extract v_18295 96 128);
      v_18387 <- eval (extract v_18305 96 128);
      v_18397 <- eval (extract v_18285 128 160);
      v_18405 <- eval (extract v_18295 128 160);
      v_18414 <- eval (extract v_18305 128 160);
      v_18424 <- eval (extract v_18285 160 192);
      v_18432 <- eval (extract v_18295 160 192);
      v_18441 <- eval (extract v_18305 160 192);
      v_18451 <- eval (extract v_18285 192 224);
      v_18459 <- eval (extract v_18295 192 224);
      v_18468 <- eval (extract v_18305 192 224);
      v_18478 <- eval (extract v_18285 224 256);
      v_18486 <- eval (extract v_18295 224 256);
      v_18495 <- eval (extract v_18305 224 256);
      setRegister (lhs.of_reg v_2791) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18286 0 1)) (uvalueMInt (extract v_18286 1 9)) (uvalueMInt (extract v_18286 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18296 0 1)) (uvalueMInt (extract v_18296 1 9)) (uvalueMInt (extract v_18296 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18306 0 1)) (uvalueMInt (extract v_18306 1 9)) (uvalueMInt (extract v_18306 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18316 0 1)) (uvalueMInt (extract v_18316 1 9)) (uvalueMInt (extract v_18316 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18324 0 1)) (uvalueMInt (extract v_18324 1 9)) (uvalueMInt (extract v_18324 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18333 0 1)) (uvalueMInt (extract v_18333 1 9)) (uvalueMInt (extract v_18333 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18343 0 1)) (uvalueMInt (extract v_18343 1 9)) (uvalueMInt (extract v_18343 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18351 0 1)) (uvalueMInt (extract v_18351 1 9)) (uvalueMInt (extract v_18351 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18360 0 1)) (uvalueMInt (extract v_18360 1 9)) (uvalueMInt (extract v_18360 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18370 0 1)) (uvalueMInt (extract v_18370 1 9)) (uvalueMInt (extract v_18370 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18378 0 1)) (uvalueMInt (extract v_18378 1 9)) (uvalueMInt (extract v_18378 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18387 0 1)) (uvalueMInt (extract v_18387 1 9)) (uvalueMInt (extract v_18387 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18397 0 1)) (uvalueMInt (extract v_18397 1 9)) (uvalueMInt (extract v_18397 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18405 0 1)) (uvalueMInt (extract v_18405 1 9)) (uvalueMInt (extract v_18405 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18414 0 1)) (uvalueMInt (extract v_18414 1 9)) (uvalueMInt (extract v_18414 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18424 0 1)) (uvalueMInt (extract v_18424 1 9)) (uvalueMInt (extract v_18424 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18432 0 1)) (uvalueMInt (extract v_18432 1 9)) (uvalueMInt (extract v_18432 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18441 0 1)) (uvalueMInt (extract v_18441 1 9)) (uvalueMInt (extract v_18441 9 32)))) 32) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18451 0 1)) (uvalueMInt (extract v_18451 1 9)) (uvalueMInt (extract v_18451 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18459 0 1)) (uvalueMInt (extract v_18459 1 9)) (uvalueMInt (extract v_18459 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18468 0 1)) (uvalueMInt (extract v_18468 1 9)) (uvalueMInt (extract v_18468 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18478 0 1)) (uvalueMInt (extract v_18478 1 9)) (uvalueMInt (extract v_18478 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18486 0 1)) (uvalueMInt (extract v_18486 1 9)) (uvalueMInt (extract v_18486 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18495 0 1)) (uvalueMInt (extract v_18495 1 9)) (uvalueMInt (extract v_18495 9 32)))) 32))))))));
      pure ()
    pat_end
