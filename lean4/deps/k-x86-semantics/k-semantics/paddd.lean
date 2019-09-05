def paddd1 : instruction :=
  definst "paddd" $ do
    pattern fun (v_3183 : reg (bv 128)) (v_3184 : reg (bv 128)) => do
      v_5688 <- getRegister v_3184;
      v_5690 <- getRegister v_3183;
      setRegister (lhs.of_reg v_3184) (concat (add (extract v_5688 0 32) (extract v_5690 0 32)) (concat (add (extract v_5688 32 64) (extract v_5690 32 64)) (concat (add (extract v_5688 64 96) (extract v_5690 64 96)) (add (extract v_5688 96 128) (extract v_5690 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3178 : Mem) (v_3179 : reg (bv 128)) => do
      v_9620 <- getRegister v_3179;
      v_9622 <- evaluateAddress v_3178;
      v_9623 <- load v_9622 16;
      setRegister (lhs.of_reg v_3179) (concat (add (extract v_9620 0 32) (extract v_9623 0 32)) (concat (add (extract v_9620 32 64) (extract v_9623 32 64)) (concat (add (extract v_9620 64 96) (extract v_9623 64 96)) (add (extract v_9620 96 128) (extract v_9623 96 128)))));
      pure ()
    pat_end
