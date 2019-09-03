def unpcklpd1 : instruction :=
  definst "unpcklpd" $ do
    pattern fun (v_2551 : reg (bv 128)) (v_2552 : reg (bv 128)) => do
      v_4788 <- getRegister v_2551;
      v_4790 <- getRegister v_2552;
      setRegister (lhs.of_reg v_2552) (concat (extract v_4788 64 128) (extract v_4790 64 128));
      pure ()
    pat_end;
    pattern fun (v_2544 : Mem) (v_2547 : reg (bv 128)) => do
      v_9264 <- evaluateAddress v_2544;
      v_9265 <- load v_9264 16;
      v_9267 <- getRegister v_2547;
      setRegister (lhs.of_reg v_2547) (concat (extract v_9265 64 128) (extract v_9267 64 128));
      pure ()
    pat_end
