def psadbw1 : instruction :=
  definst "psadbw" $ do
    pattern fun (v_2944 : reg (bv 128)) (v_2945 : reg (bv 128)) => do
      v_6454 <- getRegister v_2945;
      v_6455 <- eval (extract v_6454 0 8);
      v_6456 <- getRegister v_2944;
      v_6457 <- eval (extract v_6456 0 8);
      v_6463 <- eval (extract v_6454 8 16);
      v_6464 <- eval (extract v_6456 8 16);
      v_6470 <- eval (extract v_6454 16 24);
      v_6471 <- eval (extract v_6456 16 24);
      v_6477 <- eval (extract v_6454 24 32);
      v_6478 <- eval (extract v_6456 24 32);
      v_6484 <- eval (extract v_6454 32 40);
      v_6485 <- eval (extract v_6456 32 40);
      v_6491 <- eval (extract v_6454 40 48);
      v_6492 <- eval (extract v_6456 40 48);
      v_6498 <- eval (extract v_6454 48 56);
      v_6499 <- eval (extract v_6456 48 56);
      v_6505 <- eval (extract v_6454 56 64);
      v_6506 <- eval (extract v_6456 56 64);
      v_6519 <- eval (extract v_6454 64 72);
      v_6520 <- eval (extract v_6456 64 72);
      v_6526 <- eval (extract v_6454 72 80);
      v_6527 <- eval (extract v_6456 72 80);
      v_6533 <- eval (extract v_6454 80 88);
      v_6534 <- eval (extract v_6456 80 88);
      v_6540 <- eval (extract v_6454 88 96);
      v_6541 <- eval (extract v_6456 88 96);
      v_6547 <- eval (extract v_6454 96 104);
      v_6548 <- eval (extract v_6456 96 104);
      v_6554 <- eval (extract v_6454 104 112);
      v_6555 <- eval (extract v_6456 104 112);
      v_6561 <- eval (extract v_6454 112 120);
      v_6562 <- eval (extract v_6456 112 120);
      v_6568 <- eval (extract v_6454 120 128);
      v_6569 <- eval (extract v_6456 120 128);
      setRegister (lhs.of_reg v_2945) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_6455 v_6457) (sub v_6455 v_6457) (sub v_6457 v_6455))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6463 v_6464) (sub v_6463 v_6464) (sub v_6464 v_6463))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6470 v_6471) (sub v_6470 v_6471) (sub v_6471 v_6470))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6477 v_6478) (sub v_6477 v_6478) (sub v_6478 v_6477))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6484 v_6485) (sub v_6484 v_6485) (sub v_6485 v_6484))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6491 v_6492) (sub v_6491 v_6492) (sub v_6492 v_6491))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6498 v_6499) (sub v_6498 v_6499) (sub v_6499 v_6498))) (concat (expression.bv_nat 8 0) (mux (ugt v_6505 v_6506) (sub v_6505 v_6506) (sub v_6506 v_6505)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6519 v_6520) (sub v_6519 v_6520) (sub v_6520 v_6519))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6526 v_6527) (sub v_6526 v_6527) (sub v_6527 v_6526))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6533 v_6534) (sub v_6533 v_6534) (sub v_6534 v_6533))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6540 v_6541) (sub v_6540 v_6541) (sub v_6541 v_6540))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6547 v_6548) (sub v_6547 v_6548) (sub v_6548 v_6547))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6554 v_6555) (sub v_6554 v_6555) (sub v_6555 v_6554))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_6561 v_6562) (sub v_6561 v_6562) (sub v_6562 v_6561))) (concat (expression.bv_nat 8 0) (mux (ugt v_6568 v_6569) (sub v_6568 v_6569) (sub v_6569 v_6568)))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2941 : Mem) (v_2940 : reg (bv 128)) => do
      v_13185 <- getRegister v_2940;
      v_13186 <- eval (extract v_13185 0 8);
      v_13187 <- evaluateAddress v_2941;
      v_13188 <- load v_13187 16;
      v_13189 <- eval (extract v_13188 0 8);
      v_13195 <- eval (extract v_13185 8 16);
      v_13196 <- eval (extract v_13188 8 16);
      v_13202 <- eval (extract v_13185 16 24);
      v_13203 <- eval (extract v_13188 16 24);
      v_13209 <- eval (extract v_13185 24 32);
      v_13210 <- eval (extract v_13188 24 32);
      v_13216 <- eval (extract v_13185 32 40);
      v_13217 <- eval (extract v_13188 32 40);
      v_13223 <- eval (extract v_13185 40 48);
      v_13224 <- eval (extract v_13188 40 48);
      v_13230 <- eval (extract v_13185 48 56);
      v_13231 <- eval (extract v_13188 48 56);
      v_13237 <- eval (extract v_13185 56 64);
      v_13238 <- eval (extract v_13188 56 64);
      v_13251 <- eval (extract v_13185 64 72);
      v_13252 <- eval (extract v_13188 64 72);
      v_13258 <- eval (extract v_13185 72 80);
      v_13259 <- eval (extract v_13188 72 80);
      v_13265 <- eval (extract v_13185 80 88);
      v_13266 <- eval (extract v_13188 80 88);
      v_13272 <- eval (extract v_13185 88 96);
      v_13273 <- eval (extract v_13188 88 96);
      v_13279 <- eval (extract v_13185 96 104);
      v_13280 <- eval (extract v_13188 96 104);
      v_13286 <- eval (extract v_13185 104 112);
      v_13287 <- eval (extract v_13188 104 112);
      v_13293 <- eval (extract v_13185 112 120);
      v_13294 <- eval (extract v_13188 112 120);
      v_13300 <- eval (extract v_13185 120 128);
      v_13301 <- eval (extract v_13188 120 128);
      setRegister (lhs.of_reg v_2940) (concat (expression.bv_nat 48 0) (concat (add (concat (expression.bv_nat 8 0) (mux (ugt v_13186 v_13189) (sub v_13186 v_13189) (sub v_13189 v_13186))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13195 v_13196) (sub v_13195 v_13196) (sub v_13196 v_13195))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13202 v_13203) (sub v_13202 v_13203) (sub v_13203 v_13202))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13209 v_13210) (sub v_13209 v_13210) (sub v_13210 v_13209))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13216 v_13217) (sub v_13216 v_13217) (sub v_13217 v_13216))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13223 v_13224) (sub v_13223 v_13224) (sub v_13224 v_13223))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13230 v_13231) (sub v_13230 v_13231) (sub v_13231 v_13230))) (concat (expression.bv_nat 8 0) (mux (ugt v_13237 v_13238) (sub v_13237 v_13238) (sub v_13238 v_13237)))))))))) (concat (expression.bv_nat 48 0) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13251 v_13252) (sub v_13251 v_13252) (sub v_13252 v_13251))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13258 v_13259) (sub v_13258 v_13259) (sub v_13259 v_13258))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13265 v_13266) (sub v_13265 v_13266) (sub v_13266 v_13265))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13272 v_13273) (sub v_13272 v_13273) (sub v_13273 v_13272))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13279 v_13280) (sub v_13279 v_13280) (sub v_13280 v_13279))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13286 v_13287) (sub v_13286 v_13287) (sub v_13287 v_13286))) (add (concat (expression.bv_nat 8 0) (mux (ugt v_13293 v_13294) (sub v_13293 v_13294) (sub v_13294 v_13293))) (concat (expression.bv_nat 8 0) (mux (ugt v_13300 v_13301) (sub v_13300 v_13301) (sub v_13301 v_13300)))))))))))));
      pure ()
    pat_end
