def paddd1 : instruction :=
  definst "paddd" $ do
    pattern fun (v_3208 : reg (bv 128)) (v_3209 : reg (bv 128)) => do
      v_5715 <- getRegister v_3209;
      v_5717 <- getRegister v_3208;
      setRegister (lhs.of_reg v_3209) (concat (add (extract v_5715 0 32) (extract v_5717 0 32)) (concat (add (extract v_5715 32 64) (extract v_5717 32 64)) (concat (add (extract v_5715 64 96) (extract v_5717 64 96)) (add (extract v_5715 96 128) (extract v_5717 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3204 : Mem) (v_3205 : reg (bv 128)) => do
      v_9647 <- getRegister v_3205;
      v_9649 <- evaluateAddress v_3204;
      v_9650 <- load v_9649 16;
      setRegister (lhs.of_reg v_3205) (concat (add (extract v_9647 0 32) (extract v_9650 0 32)) (concat (add (extract v_9647 32 64) (extract v_9650 32 64)) (concat (add (extract v_9647 64 96) (extract v_9650 64 96)) (add (extract v_9647 96 128) (extract v_9650 96 128)))));
      pure ()
    pat_end
