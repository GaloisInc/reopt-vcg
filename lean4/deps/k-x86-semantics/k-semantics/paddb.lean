def paddb1 : instruction :=
  definst "paddb" $ do
    pattern fun (v_3199 : reg (bv 128)) (v_3200 : reg (bv 128)) => do
      v_5645 <- getRegister v_3200;
      v_5647 <- getRegister v_3199;
      setRegister (lhs.of_reg v_3200) (concat (add (extract v_5645 0 8) (extract v_5647 0 8)) (concat (add (extract v_5645 8 16) (extract v_5647 8 16)) (concat (add (extract v_5645 16 24) (extract v_5647 16 24)) (concat (add (extract v_5645 24 32) (extract v_5647 24 32)) (concat (add (extract v_5645 32 40) (extract v_5647 32 40)) (concat (add (extract v_5645 40 48) (extract v_5647 40 48)) (concat (add (extract v_5645 48 56) (extract v_5647 48 56)) (concat (add (extract v_5645 56 64) (extract v_5647 56 64)) (concat (add (extract v_5645 64 72) (extract v_5647 64 72)) (concat (add (extract v_5645 72 80) (extract v_5647 72 80)) (concat (add (extract v_5645 80 88) (extract v_5647 80 88)) (concat (add (extract v_5645 88 96) (extract v_5647 88 96)) (concat (add (extract v_5645 96 104) (extract v_5647 96 104)) (concat (add (extract v_5645 104 112) (extract v_5647 104 112)) (concat (add (extract v_5645 112 120) (extract v_5647 112 120)) (add (extract v_5645 120 128) (extract v_5647 120 128)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3195 : Mem) (v_3196 : reg (bv 128)) => do
      v_9580 <- getRegister v_3196;
      v_9582 <- evaluateAddress v_3195;
      v_9583 <- load v_9582 16;
      setRegister (lhs.of_reg v_3196) (concat (add (extract v_9580 0 8) (extract v_9583 0 8)) (concat (add (extract v_9580 8 16) (extract v_9583 8 16)) (concat (add (extract v_9580 16 24) (extract v_9583 16 24)) (concat (add (extract v_9580 24 32) (extract v_9583 24 32)) (concat (add (extract v_9580 32 40) (extract v_9583 32 40)) (concat (add (extract v_9580 40 48) (extract v_9583 40 48)) (concat (add (extract v_9580 48 56) (extract v_9583 48 56)) (concat (add (extract v_9580 56 64) (extract v_9583 56 64)) (concat (add (extract v_9580 64 72) (extract v_9583 64 72)) (concat (add (extract v_9580 72 80) (extract v_9583 72 80)) (concat (add (extract v_9580 80 88) (extract v_9583 80 88)) (concat (add (extract v_9580 88 96) (extract v_9583 88 96)) (concat (add (extract v_9580 96 104) (extract v_9583 96 104)) (concat (add (extract v_9580 104 112) (extract v_9583 104 112)) (concat (add (extract v_9580 112 120) (extract v_9583 112 120)) (add (extract v_9580 120 128) (extract v_9583 120 128)))))))))))))))));
      pure ()
    pat_end
