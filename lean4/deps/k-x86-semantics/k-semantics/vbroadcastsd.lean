def vbroadcastsd1 : instruction :=
  definst "vbroadcastsd" $ do
    pattern fun (v_2971 : reg (bv 128)) (v_2967 : reg (bv 256)) => do
      v_5487 <- getRegister v_2971;
      v_5488 <- eval (extract v_5487 64 128);
      setRegister (lhs.of_reg v_2967) (concat (concat (concat v_5488 v_5488) v_5488) v_5488);
      pure ()
    pat_end;
    pattern fun (v_2963 : Mem) (v_2964 : reg (bv 256)) => do
      v_9683 <- evaluateAddress v_2963;
      v_9684 <- load v_9683 8;
      setRegister (lhs.of_reg v_2964) (concat (concat (concat v_9684 v_9684) v_9684) v_9684);
      pure ()
    pat_end
