def vfmaddsub213ps1 : instruction :=
  definst "vfmaddsub213ps" $ do
    pattern fun (v_2695 : reg (bv 128)) (v_2696 : reg (bv 128)) (v_2697 : reg (bv 128)) => do
      v_6282 <- getRegister v_2696;
      v_6283 <- eval (extract v_6282 0 32);
      v_6291 <- getRegister v_2697;
      v_6292 <- eval (extract v_6291 0 32);
      v_6301 <- getRegister v_2695;
      v_6302 <- eval (extract v_6301 0 32);
      v_6312 <- eval (extract v_6282 32 64);
      v_6320 <- eval (extract v_6291 32 64);
      v_6329 <- eval (extract v_6301 32 64);
      v_6340 <- eval (extract v_6282 64 96);
      v_6348 <- eval (extract v_6291 64 96);
      v_6357 <- eval (extract v_6301 64 96);
      v_6367 <- eval (extract v_6282 96 128);
      v_6375 <- eval (extract v_6291 96 128);
      v_6384 <- eval (extract v_6301 96 128);
      setRegister (lhs.of_reg v_2697) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6283 0 1)) (uvalueMInt (extract v_6283 1 9)) (uvalueMInt (extract v_6283 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6292 0 1)) (uvalueMInt (extract v_6292 1 9)) (uvalueMInt (extract v_6292 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6302 0 1)) (uvalueMInt (extract v_6302 1 9)) (uvalueMInt (extract v_6302 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6312 0 1)) (uvalueMInt (extract v_6312 1 9)) (uvalueMInt (extract v_6312 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6320 0 1)) (uvalueMInt (extract v_6320 1 9)) (uvalueMInt (extract v_6320 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6329 0 1)) (uvalueMInt (extract v_6329 1 9)) (uvalueMInt (extract v_6329 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6340 0 1)) (uvalueMInt (extract v_6340 1 9)) (uvalueMInt (extract v_6340 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6348 0 1)) (uvalueMInt (extract v_6348 1 9)) (uvalueMInt (extract v_6348 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6357 0 1)) (uvalueMInt (extract v_6357 1 9)) (uvalueMInt (extract v_6357 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6367 0 1)) (uvalueMInt (extract v_6367 1 9)) (uvalueMInt (extract v_6367 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6375 0 1)) (uvalueMInt (extract v_6375 1 9)) (uvalueMInt (extract v_6375 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6384 0 1)) (uvalueMInt (extract v_6384 1 9)) (uvalueMInt (extract v_6384 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2706 : reg (bv 256)) (v_2707 : reg (bv 256)) (v_2708 : reg (bv 256)) => do
      v_6402 <- getRegister v_2707;
      v_6403 <- eval (extract v_6402 0 32);
      v_6411 <- getRegister v_2708;
      v_6412 <- eval (extract v_6411 0 32);
      v_6421 <- getRegister v_2706;
      v_6422 <- eval (extract v_6421 0 32);
      v_6432 <- eval (extract v_6402 32 64);
      v_6440 <- eval (extract v_6411 32 64);
      v_6449 <- eval (extract v_6421 32 64);
      v_6460 <- eval (extract v_6402 64 96);
      v_6468 <- eval (extract v_6411 64 96);
      v_6477 <- eval (extract v_6421 64 96);
      v_6487 <- eval (extract v_6402 96 128);
      v_6495 <- eval (extract v_6411 96 128);
      v_6504 <- eval (extract v_6421 96 128);
      v_6515 <- eval (extract v_6402 128 160);
      v_6523 <- eval (extract v_6411 128 160);
      v_6532 <- eval (extract v_6421 128 160);
      v_6542 <- eval (extract v_6402 160 192);
      v_6550 <- eval (extract v_6411 160 192);
      v_6559 <- eval (extract v_6421 160 192);
      v_6570 <- eval (extract v_6402 192 224);
      v_6578 <- eval (extract v_6411 192 224);
      v_6587 <- eval (extract v_6421 192 224);
      v_6597 <- eval (extract v_6402 224 256);
      v_6605 <- eval (extract v_6411 224 256);
      v_6614 <- eval (extract v_6421 224 256);
      setRegister (lhs.of_reg v_2708) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6403 0 1)) (uvalueMInt (extract v_6403 1 9)) (uvalueMInt (extract v_6403 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6412 0 1)) (uvalueMInt (extract v_6412 1 9)) (uvalueMInt (extract v_6412 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6422 0 1)) (uvalueMInt (extract v_6422 1 9)) (uvalueMInt (extract v_6422 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6432 0 1)) (uvalueMInt (extract v_6432 1 9)) (uvalueMInt (extract v_6432 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6440 0 1)) (uvalueMInt (extract v_6440 1 9)) (uvalueMInt (extract v_6440 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6449 0 1)) (uvalueMInt (extract v_6449 1 9)) (uvalueMInt (extract v_6449 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6460 0 1)) (uvalueMInt (extract v_6460 1 9)) (uvalueMInt (extract v_6460 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6468 0 1)) (uvalueMInt (extract v_6468 1 9)) (uvalueMInt (extract v_6468 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6477 0 1)) (uvalueMInt (extract v_6477 1 9)) (uvalueMInt (extract v_6477 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6487 0 1)) (uvalueMInt (extract v_6487 1 9)) (uvalueMInt (extract v_6487 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6495 0 1)) (uvalueMInt (extract v_6495 1 9)) (uvalueMInt (extract v_6495 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6504 0 1)) (uvalueMInt (extract v_6504 1 9)) (uvalueMInt (extract v_6504 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6515 0 1)) (uvalueMInt (extract v_6515 1 9)) (uvalueMInt (extract v_6515 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6523 0 1)) (uvalueMInt (extract v_6523 1 9)) (uvalueMInt (extract v_6523 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6532 0 1)) (uvalueMInt (extract v_6532 1 9)) (uvalueMInt (extract v_6532 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6542 0 1)) (uvalueMInt (extract v_6542 1 9)) (uvalueMInt (extract v_6542 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6550 0 1)) (uvalueMInt (extract v_6550 1 9)) (uvalueMInt (extract v_6550 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6559 0 1)) (uvalueMInt (extract v_6559 1 9)) (uvalueMInt (extract v_6559 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6570 0 1)) (uvalueMInt (extract v_6570 1 9)) (uvalueMInt (extract v_6570 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6578 0 1)) (uvalueMInt (extract v_6578 1 9)) (uvalueMInt (extract v_6578 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6587 0 1)) (uvalueMInt (extract v_6587 1 9)) (uvalueMInt (extract v_6587 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6597 0 1)) (uvalueMInt (extract v_6597 1 9)) (uvalueMInt (extract v_6597 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6605 0 1)) (uvalueMInt (extract v_6605 1 9)) (uvalueMInt (extract v_6605 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6614 0 1)) (uvalueMInt (extract v_6614 1 9)) (uvalueMInt (extract v_6614 9 32)))) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2692 : Mem) (v_2690 : reg (bv 128)) (v_2691 : reg (bv 128)) => do
      v_17129 <- getRegister v_2690;
      v_17130 <- eval (extract v_17129 0 32);
      v_17138 <- getRegister v_2691;
      v_17139 <- eval (extract v_17138 0 32);
      v_17148 <- evaluateAddress v_2692;
      v_17149 <- load v_17148 16;
      v_17150 <- eval (extract v_17149 0 32);
      v_17160 <- eval (extract v_17129 32 64);
      v_17168 <- eval (extract v_17138 32 64);
      v_17177 <- eval (extract v_17149 32 64);
      v_17188 <- eval (extract v_17129 64 96);
      v_17196 <- eval (extract v_17138 64 96);
      v_17205 <- eval (extract v_17149 64 96);
      v_17215 <- eval (extract v_17129 96 128);
      v_17223 <- eval (extract v_17138 96 128);
      v_17232 <- eval (extract v_17149 96 128);
      setRegister (lhs.of_reg v_2691) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17130 0 1)) (uvalueMInt (extract v_17130 1 9)) (uvalueMInt (extract v_17130 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17139 0 1)) (uvalueMInt (extract v_17139 1 9)) (uvalueMInt (extract v_17139 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17150 0 1)) (uvalueMInt (extract v_17150 1 9)) (uvalueMInt (extract v_17150 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17160 0 1)) (uvalueMInt (extract v_17160 1 9)) (uvalueMInt (extract v_17160 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17168 0 1)) (uvalueMInt (extract v_17168 1 9)) (uvalueMInt (extract v_17168 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17177 0 1)) (uvalueMInt (extract v_17177 1 9)) (uvalueMInt (extract v_17177 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17188 0 1)) (uvalueMInt (extract v_17188 1 9)) (uvalueMInt (extract v_17188 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17196 0 1)) (uvalueMInt (extract v_17196 1 9)) (uvalueMInt (extract v_17196 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17205 0 1)) (uvalueMInt (extract v_17205 1 9)) (uvalueMInt (extract v_17205 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17215 0 1)) (uvalueMInt (extract v_17215 1 9)) (uvalueMInt (extract v_17215 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17223 0 1)) (uvalueMInt (extract v_17223 1 9)) (uvalueMInt (extract v_17223 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17232 0 1)) (uvalueMInt (extract v_17232 1 9)) (uvalueMInt (extract v_17232 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2701 : Mem) (v_2702 : reg (bv 256)) (v_2703 : reg (bv 256)) => do
      v_17245 <- getRegister v_2702;
      v_17246 <- eval (extract v_17245 0 32);
      v_17254 <- getRegister v_2703;
      v_17255 <- eval (extract v_17254 0 32);
      v_17264 <- evaluateAddress v_2701;
      v_17265 <- load v_17264 32;
      v_17266 <- eval (extract v_17265 0 32);
      v_17276 <- eval (extract v_17245 32 64);
      v_17284 <- eval (extract v_17254 32 64);
      v_17293 <- eval (extract v_17265 32 64);
      v_17304 <- eval (extract v_17245 64 96);
      v_17312 <- eval (extract v_17254 64 96);
      v_17321 <- eval (extract v_17265 64 96);
      v_17331 <- eval (extract v_17245 96 128);
      v_17339 <- eval (extract v_17254 96 128);
      v_17348 <- eval (extract v_17265 96 128);
      v_17359 <- eval (extract v_17245 128 160);
      v_17367 <- eval (extract v_17254 128 160);
      v_17376 <- eval (extract v_17265 128 160);
      v_17386 <- eval (extract v_17245 160 192);
      v_17394 <- eval (extract v_17254 160 192);
      v_17403 <- eval (extract v_17265 160 192);
      v_17414 <- eval (extract v_17245 192 224);
      v_17422 <- eval (extract v_17254 192 224);
      v_17431 <- eval (extract v_17265 192 224);
      v_17441 <- eval (extract v_17245 224 256);
      v_17449 <- eval (extract v_17254 224 256);
      v_17458 <- eval (extract v_17265 224 256);
      setRegister (lhs.of_reg v_2703) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17246 0 1)) (uvalueMInt (extract v_17246 1 9)) (uvalueMInt (extract v_17246 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17255 0 1)) (uvalueMInt (extract v_17255 1 9)) (uvalueMInt (extract v_17255 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17266 0 1)) (uvalueMInt (extract v_17266 1 9)) (uvalueMInt (extract v_17266 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17276 0 1)) (uvalueMInt (extract v_17276 1 9)) (uvalueMInt (extract v_17276 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17284 0 1)) (uvalueMInt (extract v_17284 1 9)) (uvalueMInt (extract v_17284 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17293 0 1)) (uvalueMInt (extract v_17293 1 9)) (uvalueMInt (extract v_17293 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17304 0 1)) (uvalueMInt (extract v_17304 1 9)) (uvalueMInt (extract v_17304 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17312 0 1)) (uvalueMInt (extract v_17312 1 9)) (uvalueMInt (extract v_17312 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17321 0 1)) (uvalueMInt (extract v_17321 1 9)) (uvalueMInt (extract v_17321 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17331 0 1)) (uvalueMInt (extract v_17331 1 9)) (uvalueMInt (extract v_17331 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17339 0 1)) (uvalueMInt (extract v_17339 1 9)) (uvalueMInt (extract v_17339 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17348 0 1)) (uvalueMInt (extract v_17348 1 9)) (uvalueMInt (extract v_17348 9 32)))) 32)) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17359 0 1)) (uvalueMInt (extract v_17359 1 9)) (uvalueMInt (extract v_17359 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17367 0 1)) (uvalueMInt (extract v_17367 1 9)) (uvalueMInt (extract v_17367 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17376 0 1)) (uvalueMInt (extract v_17376 1 9)) (uvalueMInt (extract v_17376 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17386 0 1)) (uvalueMInt (extract v_17386 1 9)) (uvalueMInt (extract v_17386 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17394 0 1)) (uvalueMInt (extract v_17394 1 9)) (uvalueMInt (extract v_17394 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17403 0 1)) (uvalueMInt (extract v_17403 1 9)) (uvalueMInt (extract v_17403 9 32)))) 32)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17414 0 1)) (uvalueMInt (extract v_17414 1 9)) (uvalueMInt (extract v_17414 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17422 0 1)) (uvalueMInt (extract v_17422 1 9)) (uvalueMInt (extract v_17422 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17431 0 1)) (uvalueMInt (extract v_17431 1 9)) (uvalueMInt (extract v_17431 9 32)))) 32) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17441 0 1)) (uvalueMInt (extract v_17441 1 9)) (uvalueMInt (extract v_17441 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17449 0 1)) (uvalueMInt (extract v_17449 1 9)) (uvalueMInt (extract v_17449 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_17458 0 1)) (uvalueMInt (extract v_17458 1 9)) (uvalueMInt (extract v_17458 9 32)))) 32)))));
      pure ()
    pat_end
