def vmaskmovps1 : instruction :=
  definst "vmaskmovps" $ do
    pattern fun (v_2536 : Mem) (v_2537 : reg (bv 128)) (v_2538 : reg (bv 128)) => do
      v_10717 <- getRegister v_2537;
      v_10720 <- evaluateAddress v_2536;
      v_10721 <- load v_10720 16;
      setRegister (lhs.of_reg v_2538) (concat (mux (eq (extract v_10717 0 1) (expression.bv_nat 1 1)) (extract v_10721 0 32) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10717 32 33) (expression.bv_nat 1 1)) (extract v_10721 32 64) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10717 64 65) (expression.bv_nat 1 1)) (extract v_10721 64 96) (expression.bv_nat 32 0)) (mux (eq (extract v_10717 96 97) (expression.bv_nat 1 1)) (extract v_10721 96 128) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2541 : Mem) (v_2542 : reg (bv 256)) (v_2543 : reg (bv 256)) => do
      v_10740 <- getRegister v_2542;
      v_10743 <- evaluateAddress v_2541;
      v_10744 <- load v_10743 32;
      setRegister (lhs.of_reg v_2543) (concat (mux (eq (extract v_10740 0 1) (expression.bv_nat 1 1)) (extract v_10744 0 32) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10740 32 33) (expression.bv_nat 1 1)) (extract v_10744 32 64) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10740 64 65) (expression.bv_nat 1 1)) (extract v_10744 64 96) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10740 96 97) (expression.bv_nat 1 1)) (extract v_10744 96 128) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10740 128 129) (expression.bv_nat 1 1)) (extract v_10744 128 160) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10740 160 161) (expression.bv_nat 1 1)) (extract v_10744 160 192) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10740 192 193) (expression.bv_nat 1 1)) (extract v_10744 192 224) (expression.bv_nat 32 0)) (mux (eq (extract v_10740 224 225) (expression.bv_nat 1 1)) (extract v_10744 224 256) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2527 : reg (bv 128)) (v_2528 : reg (bv 128)) (v_2526 : Mem) => do
      v_13519 <- evaluateAddress v_2526;
      v_13520 <- getRegister v_2528;
      v_13523 <- getRegister v_2527;
      v_13525 <- load v_13519 16;
      store v_13519 (concat (mux (eq (extract v_13520 0 1) (expression.bv_nat 1 1)) (extract v_13523 0 32) (extract v_13525 0 32)) (concat (mux (eq (extract v_13520 32 33) (expression.bv_nat 1 1)) (extract v_13523 32 64) (extract v_13525 32 64)) (concat (mux (eq (extract v_13520 64 65) (expression.bv_nat 1 1)) (extract v_13523 64 96) (extract v_13525 64 96)) (mux (eq (extract v_13520 96 97) (expression.bv_nat 1 1)) (extract v_13523 96 128) (extract v_13525 96 128))))) 16;
      pure ()
    pat_end;
    pattern fun (v_2532 : reg (bv 256)) (v_2533 : reg (bv 256)) (v_2531 : Mem) => do
      v_13547 <- evaluateAddress v_2531;
      v_13548 <- getRegister v_2533;
      v_13551 <- getRegister v_2532;
      v_13553 <- load v_13547 32;
      store v_13547 (concat (mux (eq (extract v_13548 0 1) (expression.bv_nat 1 1)) (extract v_13551 0 32) (extract v_13553 0 32)) (concat (mux (eq (extract v_13548 32 33) (expression.bv_nat 1 1)) (extract v_13551 32 64) (extract v_13553 32 64)) (concat (mux (eq (extract v_13548 64 65) (expression.bv_nat 1 1)) (extract v_13551 64 96) (extract v_13553 64 96)) (concat (mux (eq (extract v_13548 96 97) (expression.bv_nat 1 1)) (extract v_13551 96 128) (extract v_13553 96 128)) (concat (mux (eq (extract v_13548 128 129) (expression.bv_nat 1 1)) (extract v_13551 128 160) (extract v_13553 128 160)) (concat (mux (eq (extract v_13548 160 161) (expression.bv_nat 1 1)) (extract v_13551 160 192) (extract v_13553 160 192)) (concat (mux (eq (extract v_13548 192 193) (expression.bv_nat 1 1)) (extract v_13551 192 224) (extract v_13553 192 224)) (mux (eq (extract v_13548 224 225) (expression.bv_nat 1 1)) (extract v_13551 224 256) (extract v_13553 224 256))))))))) 32;
      pure ()
    pat_end
