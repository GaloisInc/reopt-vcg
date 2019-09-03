def vmaskmovpd1 : instruction :=
  definst "vmaskmovpd" $ do
    pattern fun (v_2516 : Mem) (v_2517 : reg (bv 128)) (v_2518 : reg (bv 128)) => do
      v_10679 <- getRegister v_2517;
      v_10682 <- evaluateAddress v_2516;
      v_10683 <- load v_10682 16;
      setRegister (lhs.of_reg v_2518) (concat (mux (eq (extract v_10679 0 1) (expression.bv_nat 1 1)) (extract v_10683 0 64) (expression.bv_nat 64 0)) (mux (eq (extract v_10679 64 65) (expression.bv_nat 1 1)) (extract v_10683 64 128) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2521 : Mem) (v_2522 : reg (bv 256)) (v_2523 : reg (bv 256)) => do
      v_10692 <- getRegister v_2522;
      v_10695 <- evaluateAddress v_2521;
      v_10696 <- load v_10695 32;
      setRegister (lhs.of_reg v_2523) (concat (mux (eq (extract v_10692 0 1) (expression.bv_nat 1 1)) (extract v_10696 0 64) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_10692 64 65) (expression.bv_nat 1 1)) (extract v_10696 64 128) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_10692 128 129) (expression.bv_nat 1 1)) (extract v_10696 128 192) (expression.bv_nat 64 0)) (mux (eq (extract v_10692 192 193) (expression.bv_nat 1 1)) (extract v_10696 192 256) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (v_2507 : reg (bv 128)) (v_2508 : reg (bv 128)) (v_2506 : Mem) => do
      v_13475 <- evaluateAddress v_2506;
      v_13476 <- getRegister v_2508;
      v_13479 <- getRegister v_2507;
      v_13481 <- load v_13475 16;
      store v_13475 (concat (mux (eq (extract v_13476 0 1) (expression.bv_nat 1 1)) (extract v_13479 0 64) (extract v_13481 0 64)) (mux (eq (extract v_13476 64 65) (expression.bv_nat 1 1)) (extract v_13479 64 128) (extract v_13481 64 128))) 16;
      pure ()
    pat_end;
    pattern fun (v_2512 : reg (bv 256)) (v_2513 : reg (bv 256)) (v_2511 : Mem) => do
      v_13491 <- evaluateAddress v_2511;
      v_13492 <- getRegister v_2513;
      v_13495 <- getRegister v_2512;
      v_13497 <- load v_13491 32;
      store v_13491 (concat (mux (eq (extract v_13492 0 1) (expression.bv_nat 1 1)) (extract v_13495 0 64) (extract v_13497 0 64)) (concat (mux (eq (extract v_13492 64 65) (expression.bv_nat 1 1)) (extract v_13495 64 128) (extract v_13497 64 128)) (concat (mux (eq (extract v_13492 128 129) (expression.bv_nat 1 1)) (extract v_13495 128 192) (extract v_13497 128 192)) (mux (eq (extract v_13492 192 193) (expression.bv_nat 1 1)) (extract v_13495 192 256) (extract v_13497 192 256))))) 32;
      pure ()
    pat_end
