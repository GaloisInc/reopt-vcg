def vmaskmovps1 : instruction :=
  definst "vmaskmovps" $ do
    pattern fun (v_2612 : Mem) (v_2613 : reg (bv 128)) (v_2614 : reg (bv 128)) => do
      v_9817 <- getRegister v_2613;
      v_9819 <- evaluateAddress v_2612;
      v_9820 <- load v_9819 16;
      setRegister (lhs.of_reg v_2614) (concat (mux (isBitSet v_9817 0) (extract v_9820 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9817 32) (extract v_9820 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9817 64) (extract v_9820 64 96) (expression.bv_nat 32 0)) (mux (isBitSet v_9817 96) (extract v_9820 96 128) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2617 : Mem) (v_2618 : reg (bv 256)) (v_2619 : reg (bv 256)) => do
      v_9836 <- getRegister v_2618;
      v_9838 <- evaluateAddress v_2617;
      v_9839 <- load v_9838 32;
      setRegister (lhs.of_reg v_2619) (concat (mux (isBitSet v_9836 0) (extract v_9839 0 32) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9836 32) (extract v_9839 32 64) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9836 64) (extract v_9839 64 96) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9836 96) (extract v_9839 96 128) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9836 128) (extract v_9839 128 160) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9836 160) (extract v_9839 160 192) (expression.bv_nat 32 0)) (concat (mux (isBitSet v_9836 192) (extract v_9839 192 224) (expression.bv_nat 32 0)) (mux (isBitSet v_9836 224) (extract v_9839 224 256) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2603 : reg (bv 128)) (v_2604 : reg (bv 128)) (v_2602 : Mem) => do
      v_12361 <- evaluateAddress v_2602;
      v_12362 <- getRegister v_2604;
      v_12364 <- getRegister v_2603;
      v_12366 <- load v_12361 16;
      store v_12361 (concat (mux (isBitSet v_12362 0) (extract v_12364 0 32) (extract v_12366 0 32)) (concat (mux (isBitSet v_12362 32) (extract v_12364 32 64) (extract v_12366 32 64)) (concat (mux (isBitSet v_12362 64) (extract v_12364 64 96) (extract v_12366 64 96)) (mux (isBitSet v_12362 96) (extract v_12364 96 128) (extract v_12366 96 128))))) 16;
      pure ()
    pat_end;
    pattern fun (v_2608 : reg (bv 256)) (v_2609 : reg (bv 256)) (v_2607 : Mem) => do
      v_12385 <- evaluateAddress v_2607;
      v_12386 <- getRegister v_2609;
      v_12388 <- getRegister v_2608;
      v_12390 <- load v_12385 32;
      store v_12385 (concat (mux (isBitSet v_12386 0) (extract v_12388 0 32) (extract v_12390 0 32)) (concat (mux (isBitSet v_12386 32) (extract v_12388 32 64) (extract v_12390 32 64)) (concat (mux (isBitSet v_12386 64) (extract v_12388 64 96) (extract v_12390 64 96)) (concat (mux (isBitSet v_12386 96) (extract v_12388 96 128) (extract v_12390 96 128)) (concat (mux (isBitSet v_12386 128) (extract v_12388 128 160) (extract v_12390 128 160)) (concat (mux (isBitSet v_12386 160) (extract v_12388 160 192) (extract v_12390 160 192)) (concat (mux (isBitSet v_12386 192) (extract v_12388 192 224) (extract v_12390 192 224)) (mux (isBitSet v_12386 224) (extract v_12388 224 256) (extract v_12390 224 256))))))))) 32;
      pure ()
    pat_end
