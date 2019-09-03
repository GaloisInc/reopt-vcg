def vpaddusw1 : instruction :=
  definst "vpaddusw" $ do
    pattern fun (v_2462 : reg (bv 128)) (v_2463 : reg (bv 128)) (v_2464 : reg (bv 128)) => do
      v_5326 <- getRegister v_2463;
      v_5329 <- getRegister v_2462;
      v_5332 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5326 0 16)) (concat (expression.bv_nat 1 0) (extract v_5329 0 16)));
      v_5341 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5326 16 32)) (concat (expression.bv_nat 1 0) (extract v_5329 16 32)));
      v_5350 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5326 32 48)) (concat (expression.bv_nat 1 0) (extract v_5329 32 48)));
      v_5359 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5326 48 64)) (concat (expression.bv_nat 1 0) (extract v_5329 48 64)));
      v_5368 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5326 64 80)) (concat (expression.bv_nat 1 0) (extract v_5329 64 80)));
      v_5377 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5326 80 96)) (concat (expression.bv_nat 1 0) (extract v_5329 80 96)));
      v_5386 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5326 96 112)) (concat (expression.bv_nat 1 0) (extract v_5329 96 112)));
      v_5395 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5326 112 128)) (concat (expression.bv_nat 1 0) (extract v_5329 112 128)));
      setRegister (lhs.of_reg v_2464) (concat (mux (eq (extract v_5332 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5332 1 17)) (concat (mux (eq (extract v_5341 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5341 1 17)) (concat (mux (eq (extract v_5350 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5350 1 17)) (concat (mux (eq (extract v_5359 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5359 1 17)) (concat (mux (eq (extract v_5368 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5368 1 17)) (concat (mux (eq (extract v_5377 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5377 1 17)) (concat (mux (eq (extract v_5386 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5386 1 17)) (mux (eq (extract v_5395 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5395 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_2476 : reg (bv 256)) (v_2477 : reg (bv 256)) (v_2478 : reg (bv 256)) => do
      v_5413 <- getRegister v_2477;
      v_5416 <- getRegister v_2476;
      v_5419 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 0 16)) (concat (expression.bv_nat 1 0) (extract v_5416 0 16)));
      v_5428 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 16 32)) (concat (expression.bv_nat 1 0) (extract v_5416 16 32)));
      v_5437 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 32 48)) (concat (expression.bv_nat 1 0) (extract v_5416 32 48)));
      v_5446 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 48 64)) (concat (expression.bv_nat 1 0) (extract v_5416 48 64)));
      v_5455 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 64 80)) (concat (expression.bv_nat 1 0) (extract v_5416 64 80)));
      v_5464 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 80 96)) (concat (expression.bv_nat 1 0) (extract v_5416 80 96)));
      v_5473 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 96 112)) (concat (expression.bv_nat 1 0) (extract v_5416 96 112)));
      v_5482 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 112 128)) (concat (expression.bv_nat 1 0) (extract v_5416 112 128)));
      v_5491 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 128 144)) (concat (expression.bv_nat 1 0) (extract v_5416 128 144)));
      v_5500 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 144 160)) (concat (expression.bv_nat 1 0) (extract v_5416 144 160)));
      v_5509 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 160 176)) (concat (expression.bv_nat 1 0) (extract v_5416 160 176)));
      v_5518 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 176 192)) (concat (expression.bv_nat 1 0) (extract v_5416 176 192)));
      v_5527 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 192 208)) (concat (expression.bv_nat 1 0) (extract v_5416 192 208)));
      v_5536 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 208 224)) (concat (expression.bv_nat 1 0) (extract v_5416 208 224)));
      v_5545 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 224 240)) (concat (expression.bv_nat 1 0) (extract v_5416 224 240)));
      v_5554 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5413 240 256)) (concat (expression.bv_nat 1 0) (extract v_5416 240 256)));
      setRegister (lhs.of_reg v_2478) (concat (mux (eq (extract v_5419 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5419 1 17)) (concat (mux (eq (extract v_5428 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5428 1 17)) (concat (mux (eq (extract v_5437 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5437 1 17)) (concat (mux (eq (extract v_5446 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5446 1 17)) (concat (mux (eq (extract v_5455 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5455 1 17)) (concat (mux (eq (extract v_5464 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5464 1 17)) (concat (mux (eq (extract v_5473 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5473 1 17)) (concat (mux (eq (extract v_5482 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5482 1 17)) (concat (mux (eq (extract v_5491 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5491 1 17)) (concat (mux (eq (extract v_5500 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5500 1 17)) (concat (mux (eq (extract v_5509 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5509 1 17)) (concat (mux (eq (extract v_5518 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5518 1 17)) (concat (mux (eq (extract v_5527 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5527 1 17)) (concat (mux (eq (extract v_5536 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5536 1 17)) (concat (mux (eq (extract v_5545 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5545 1 17)) (mux (eq (extract v_5554 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_5554 1 17)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2461 : Mem) (v_2457 : reg (bv 128)) (v_2458 : reg (bv 128)) => do
      v_14310 <- getRegister v_2457;
      v_14313 <- evaluateAddress v_2461;
      v_14314 <- load v_14313 16;
      v_14317 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14310 0 16)) (concat (expression.bv_nat 1 0) (extract v_14314 0 16)));
      v_14326 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14310 16 32)) (concat (expression.bv_nat 1 0) (extract v_14314 16 32)));
      v_14335 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14310 32 48)) (concat (expression.bv_nat 1 0) (extract v_14314 32 48)));
      v_14344 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14310 48 64)) (concat (expression.bv_nat 1 0) (extract v_14314 48 64)));
      v_14353 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14310 64 80)) (concat (expression.bv_nat 1 0) (extract v_14314 64 80)));
      v_14362 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14310 80 96)) (concat (expression.bv_nat 1 0) (extract v_14314 80 96)));
      v_14371 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14310 96 112)) (concat (expression.bv_nat 1 0) (extract v_14314 96 112)));
      v_14380 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14310 112 128)) (concat (expression.bv_nat 1 0) (extract v_14314 112 128)));
      setRegister (lhs.of_reg v_2458) (concat (mux (eq (extract v_14317 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14317 1 17)) (concat (mux (eq (extract v_14326 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14326 1 17)) (concat (mux (eq (extract v_14335 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14335 1 17)) (concat (mux (eq (extract v_14344 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14344 1 17)) (concat (mux (eq (extract v_14353 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14353 1 17)) (concat (mux (eq (extract v_14362 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14362 1 17)) (concat (mux (eq (extract v_14371 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14371 1 17)) (mux (eq (extract v_14380 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14380 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_2470 : Mem) (v_2471 : reg (bv 256)) (v_2472 : reg (bv 256)) => do
      v_14393 <- getRegister v_2471;
      v_14396 <- evaluateAddress v_2470;
      v_14397 <- load v_14396 32;
      v_14400 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 0 16)) (concat (expression.bv_nat 1 0) (extract v_14397 0 16)));
      v_14409 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 16 32)) (concat (expression.bv_nat 1 0) (extract v_14397 16 32)));
      v_14418 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 32 48)) (concat (expression.bv_nat 1 0) (extract v_14397 32 48)));
      v_14427 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 48 64)) (concat (expression.bv_nat 1 0) (extract v_14397 48 64)));
      v_14436 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 64 80)) (concat (expression.bv_nat 1 0) (extract v_14397 64 80)));
      v_14445 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 80 96)) (concat (expression.bv_nat 1 0) (extract v_14397 80 96)));
      v_14454 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 96 112)) (concat (expression.bv_nat 1 0) (extract v_14397 96 112)));
      v_14463 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 112 128)) (concat (expression.bv_nat 1 0) (extract v_14397 112 128)));
      v_14472 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 128 144)) (concat (expression.bv_nat 1 0) (extract v_14397 128 144)));
      v_14481 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 144 160)) (concat (expression.bv_nat 1 0) (extract v_14397 144 160)));
      v_14490 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 160 176)) (concat (expression.bv_nat 1 0) (extract v_14397 160 176)));
      v_14499 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 176 192)) (concat (expression.bv_nat 1 0) (extract v_14397 176 192)));
      v_14508 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 192 208)) (concat (expression.bv_nat 1 0) (extract v_14397 192 208)));
      v_14517 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 208 224)) (concat (expression.bv_nat 1 0) (extract v_14397 208 224)));
      v_14526 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 224 240)) (concat (expression.bv_nat 1 0) (extract v_14397 224 240)));
      v_14535 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14393 240 256)) (concat (expression.bv_nat 1 0) (extract v_14397 240 256)));
      setRegister (lhs.of_reg v_2472) (concat (mux (eq (extract v_14400 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14400 1 17)) (concat (mux (eq (extract v_14409 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14409 1 17)) (concat (mux (eq (extract v_14418 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14418 1 17)) (concat (mux (eq (extract v_14427 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14427 1 17)) (concat (mux (eq (extract v_14436 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14436 1 17)) (concat (mux (eq (extract v_14445 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14445 1 17)) (concat (mux (eq (extract v_14454 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14454 1 17)) (concat (mux (eq (extract v_14463 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14463 1 17)) (concat (mux (eq (extract v_14472 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14472 1 17)) (concat (mux (eq (extract v_14481 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14481 1 17)) (concat (mux (eq (extract v_14490 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14490 1 17)) (concat (mux (eq (extract v_14499 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14499 1 17)) (concat (mux (eq (extract v_14508 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14508 1 17)) (concat (mux (eq (extract v_14517 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14517 1 17)) (concat (mux (eq (extract v_14526 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14526 1 17)) (mux (eq (extract v_14535 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 16 65535) (extract v_14535 1 17)))))))))))))))));
      pure ()
    pat_end
