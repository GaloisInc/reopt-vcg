def psadbw1 : instruction :=
  definst "psadbw" $ do
    pattern fun (v_2895 : reg (bv 128)) (v_2896 : reg (bv 128)) => do
      v_6423 <- getRegister v_2896;
      v_6424 <- eval (extract v_6423 0 8);
      v_6425 <- getRegister v_2895;
      v_6426 <- eval (extract v_6425 0 8);
      v_6432 <- eval (extract v_6423 8 16);
      v_6433 <- eval (extract v_6425 8 16);
      v_6439 <- eval (extract v_6423 16 24);
      v_6440 <- eval (extract v_6425 16 24);
      v_6446 <- eval (extract v_6423 24 32);
      v_6447 <- eval (extract v_6425 24 32);
      v_6453 <- eval (extract v_6423 32 40);
      v_6454 <- eval (extract v_6425 32 40);
      v_6460 <- eval (extract v_6423 40 48);
      v_6461 <- eval (extract v_6425 40 48);
      v_6467 <- eval (extract v_6423 48 56);
      v_6468 <- eval (extract v_6425 48 56);
      v_6474 <- eval (extract v_6423 56 64);
      v_6475 <- eval (extract v_6425 56 64);
      v_6488 <- eval (extract v_6423 64 72);
      v_6489 <- eval (extract v_6425 64 72);
      v_6495 <- eval (extract v_6423 72 80);
      v_6496 <- eval (extract v_6425 72 80);
      v_6502 <- eval (extract v_6423 80 88);
      v_6503 <- eval (extract v_6425 80 88);
      v_6509 <- eval (extract v_6423 88 96);
      v_6510 <- eval (extract v_6425 88 96);
      v_6516 <- eval (extract v_6423 96 104);
      v_6517 <- eval (extract v_6425 96 104);
      v_6523 <- eval (extract v_6423 104 112);
      v_6524 <- eval (extract v_6425 104 112);
      v_6530 <- eval (extract v_6423 112 120);
      v_6531 <- eval (extract v_6425 112 120);
      v_6537 <- eval (extract v_6423 120 128);
      v_6538 <- eval (extract v_6425 120 128);
      setRegister (lhs.of_reg v_2896) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_6424 v_6426) (sub v_6424 v_6426) (sub v_6426 v_6424))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6432 v_6433) (sub v_6432 v_6433) (sub v_6433 v_6432))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6439 v_6440) (sub v_6439 v_6440) (sub v_6440 v_6439))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6446 v_6447) (sub v_6446 v_6447) (sub v_6447 v_6446))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6453 v_6454) (sub v_6453 v_6454) (sub v_6454 v_6453))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6460 v_6461) (sub v_6460 v_6461) (sub v_6461 v_6460))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6467 v_6468) (sub v_6467 v_6468) (sub v_6468 v_6467))) (concat (expression.bv_nat 8 0) (mux (ugt v_6474 v_6475) (sub v_6474 v_6475) (sub v_6475 v_6474)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6488 v_6489) (sub v_6488 v_6489) (sub v_6489 v_6488))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6495 v_6496) (sub v_6495 v_6496) (sub v_6496 v_6495))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6502 v_6503) (sub v_6502 v_6503) (sub v_6503 v_6502))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6509 v_6510) (sub v_6509 v_6510) (sub v_6510 v_6509))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6516 v_6517) (sub v_6516 v_6517) (sub v_6517 v_6516))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6523 v_6524) (sub v_6523 v_6524) (sub v_6524 v_6523))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6530 v_6531) (sub v_6530 v_6531) (sub v_6531 v_6530))) (concat (expression.bv_nat 8 0) (mux (ugt v_6537 v_6538) (sub v_6537 v_6538) (sub v_6538 v_6537)))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2891 : Mem) (v_2892 : reg (bv 128)) => do
      v_13327 <- getRegister v_2892;
      v_13328 <- eval (extract v_13327 0 8);
      v_13329 <- evaluateAddress v_2891;
      v_13330 <- load v_13329 16;
      v_13331 <- eval (extract v_13330 0 8);
      v_13337 <- eval (extract v_13327 8 16);
      v_13338 <- eval (extract v_13330 8 16);
      v_13344 <- eval (extract v_13327 16 24);
      v_13345 <- eval (extract v_13330 16 24);
      v_13351 <- eval (extract v_13327 24 32);
      v_13352 <- eval (extract v_13330 24 32);
      v_13358 <- eval (extract v_13327 32 40);
      v_13359 <- eval (extract v_13330 32 40);
      v_13365 <- eval (extract v_13327 40 48);
      v_13366 <- eval (extract v_13330 40 48);
      v_13372 <- eval (extract v_13327 48 56);
      v_13373 <- eval (extract v_13330 48 56);
      v_13379 <- eval (extract v_13327 56 64);
      v_13380 <- eval (extract v_13330 56 64);
      v_13393 <- eval (extract v_13327 64 72);
      v_13394 <- eval (extract v_13330 64 72);
      v_13400 <- eval (extract v_13327 72 80);
      v_13401 <- eval (extract v_13330 72 80);
      v_13407 <- eval (extract v_13327 80 88);
      v_13408 <- eval (extract v_13330 80 88);
      v_13414 <- eval (extract v_13327 88 96);
      v_13415 <- eval (extract v_13330 88 96);
      v_13421 <- eval (extract v_13327 96 104);
      v_13422 <- eval (extract v_13330 96 104);
      v_13428 <- eval (extract v_13327 104 112);
      v_13429 <- eval (extract v_13330 104 112);
      v_13435 <- eval (extract v_13327 112 120);
      v_13436 <- eval (extract v_13330 112 120);
      v_13442 <- eval (extract v_13327 120 128);
      v_13443 <- eval (extract v_13330 120 128);
      setRegister (lhs.of_reg v_2892) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_13328 v_13331) (sub v_13328 v_13331) (sub v_13331 v_13328))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13337 v_13338) (sub v_13337 v_13338) (sub v_13338 v_13337))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13344 v_13345) (sub v_13344 v_13345) (sub v_13345 v_13344))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13351 v_13352) (sub v_13351 v_13352) (sub v_13352 v_13351))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13358 v_13359) (sub v_13358 v_13359) (sub v_13359 v_13358))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13365 v_13366) (sub v_13365 v_13366) (sub v_13366 v_13365))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13372 v_13373) (sub v_13372 v_13373) (sub v_13373 v_13372))) (concat (expression.bv_nat 8 0) (mux (ugt v_13379 v_13380) (sub v_13379 v_13380) (sub v_13380 v_13379)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13393 v_13394) (sub v_13393 v_13394) (sub v_13394 v_13393))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13400 v_13401) (sub v_13400 v_13401) (sub v_13401 v_13400))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13407 v_13408) (sub v_13407 v_13408) (sub v_13408 v_13407))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13414 v_13415) (sub v_13414 v_13415) (sub v_13415 v_13414))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13421 v_13422) (sub v_13421 v_13422) (sub v_13422 v_13421))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13428 v_13429) (sub v_13428 v_13429) (sub v_13429 v_13428))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13435 v_13436) (sub v_13435 v_13436) (sub v_13436 v_13435))) (concat (expression.bv_nat 8 0) (mux (ugt v_13442 v_13443) (sub v_13442 v_13443) (sub v_13443 v_13442)))))))))))));
      pure ()
    pat_end
