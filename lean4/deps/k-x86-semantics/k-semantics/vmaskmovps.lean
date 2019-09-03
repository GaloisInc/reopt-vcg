def vmaskmovps1 : instruction :=
  definst "vmaskmovps" $ do
    pattern fun (v_2523 : Mem) (v_2524 : reg (bv 128)) (v_2525 : reg (bv 128)) => do
      v_9912 <- getRegister v_2524;
      v_9915 <- evaluateAddress v_2523;
      v_9916 <- load v_9915 16;
      setRegister (lhs.of_reg v_2525) (concat (mux (eq (extract v_9912 0 1) (expression.bv_nat 1 1)) (extract v_9916 0 32) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_9912 32 33) (expression.bv_nat 1 1)) (extract v_9916 32 64) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_9912 64 65) (expression.bv_nat 1 1)) (extract v_9916 64 96) (expression.bv_nat 32 0)) (mux (eq (extract v_9912 96 97) (expression.bv_nat 1 1)) (extract v_9916 96 128) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2528 : Mem) (v_2529 : reg (bv 256)) (v_2530 : reg (bv 256)) => do
      v_9935 <- getRegister v_2529;
      v_9938 <- evaluateAddress v_2528;
      v_9939 <- load v_9938 32;
      setRegister (lhs.of_reg v_2530) (concat (mux (eq (extract v_9935 0 1) (expression.bv_nat 1 1)) (extract v_9939 0 32) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_9935 32 33) (expression.bv_nat 1 1)) (extract v_9939 32 64) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_9935 64 65) (expression.bv_nat 1 1)) (extract v_9939 64 96) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_9935 96 97) (expression.bv_nat 1 1)) (extract v_9939 96 128) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_9935 128 129) (expression.bv_nat 1 1)) (extract v_9939 128 160) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_9935 160 161) (expression.bv_nat 1 1)) (extract v_9939 160 192) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_9935 192 193) (expression.bv_nat 1 1)) (extract v_9939 192 224) (expression.bv_nat 32 0)) (mux (eq (extract v_9935 224 225) (expression.bv_nat 1 1)) (extract v_9939 224 256) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2514 : reg (bv 128)) (v_2515 : reg (bv 128)) (v_2513 : Mem) => do
      v_12642 <- evaluateAddress v_2513;
      v_12643 <- getRegister v_2515;
      v_12646 <- getRegister v_2514;
      v_12648 <- load v_12642 16;
      store v_12642 (concat (mux (eq (extract v_12643 0 1) (expression.bv_nat 1 1)) (extract v_12646 0 32) (extract v_12648 0 32)) (concat (mux (eq (extract v_12643 32 33) (expression.bv_nat 1 1)) (extract v_12646 32 64) (extract v_12648 32 64)) (concat (mux (eq (extract v_12643 64 65) (expression.bv_nat 1 1)) (extract v_12646 64 96) (extract v_12648 64 96)) (mux (eq (extract v_12643 96 97) (expression.bv_nat 1 1)) (extract v_12646 96 128) (extract v_12648 96 128))))) 16;
      pure ()
    pat_end;
    pattern fun (v_2519 : reg (bv 256)) (v_2520 : reg (bv 256)) (v_2518 : Mem) => do
      v_12670 <- evaluateAddress v_2518;
      v_12671 <- getRegister v_2520;
      v_12674 <- getRegister v_2519;
      v_12676 <- load v_12670 32;
      store v_12670 (concat (mux (eq (extract v_12671 0 1) (expression.bv_nat 1 1)) (extract v_12674 0 32) (extract v_12676 0 32)) (concat (mux (eq (extract v_12671 32 33) (expression.bv_nat 1 1)) (extract v_12674 32 64) (extract v_12676 32 64)) (concat (mux (eq (extract v_12671 64 65) (expression.bv_nat 1 1)) (extract v_12674 64 96) (extract v_12676 64 96)) (concat (mux (eq (extract v_12671 96 97) (expression.bv_nat 1 1)) (extract v_12674 96 128) (extract v_12676 96 128)) (concat (mux (eq (extract v_12671 128 129) (expression.bv_nat 1 1)) (extract v_12674 128 160) (extract v_12676 128 160)) (concat (mux (eq (extract v_12671 160 161) (expression.bv_nat 1 1)) (extract v_12674 160 192) (extract v_12676 160 192)) (concat (mux (eq (extract v_12671 192 193) (expression.bv_nat 1 1)) (extract v_12674 192 224) (extract v_12676 192 224)) (mux (eq (extract v_12671 224 225) (expression.bv_nat 1 1)) (extract v_12674 224 256) (extract v_12676 224 256))))))))) 32;
      pure ()
    pat_end
