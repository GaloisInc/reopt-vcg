def vunpcklps1 : instruction :=
  definst "vunpcklps" $ do
    pattern fun (v_2547 : reg (bv 128)) (v_2548 : reg (bv 128)) (v_2549 : reg (bv 128)) => do
      v_3771 <- getRegister v_2547;
      v_3773 <- getRegister v_2548;
      setRegister (lhs.of_reg v_2549) (concat (concat (concat (extract v_3771 64 96) (extract v_3773 64 96)) (extract v_3771 96 128)) (extract v_3773 96 128));
      pure ()
    pat_end;
    pattern fun (v_2559 : reg (bv 256)) (v_2560 : reg (bv 256)) (v_2561 : reg (bv 256)) => do
      v_3786 <- getRegister v_2559;
      v_3788 <- getRegister v_2560;
      setRegister (lhs.of_reg v_2561) (concat (concat (concat (concat (extract v_3786 64 96) (extract v_3788 64 96)) (extract v_3786 96 128)) (extract v_3788 96 128)) (concat (concat (concat (extract v_3786 192 224) (extract v_3788 192 224)) (extract v_3786 224 256)) (extract v_3788 224 256)));
      pure ()
    pat_end;
    pattern fun (v_2542 : Mem) (v_2543 : reg (bv 128)) (v_2544 : reg (bv 128)) => do
      v_6998 <- evaluateAddress v_2542;
      v_6999 <- load v_6998 16;
      v_7001 <- getRegister v_2543;
      setRegister (lhs.of_reg v_2544) (concat (concat (concat (extract v_6999 64 96) (extract v_7001 64 96)) (extract v_6999 96 128)) (extract v_7001 96 128));
      pure ()
    pat_end;
    pattern fun (v_2553 : Mem) (v_2554 : reg (bv 256)) (v_2555 : reg (bv 256)) => do
      v_7009 <- evaluateAddress v_2553;
      v_7010 <- load v_7009 32;
      v_7012 <- getRegister v_2554;
      setRegister (lhs.of_reg v_2555) (concat (concat (concat (concat (extract v_7010 64 96) (extract v_7012 64 96)) (extract v_7010 96 128)) (extract v_7012 96 128)) (concat (concat (concat (extract v_7010 192 224) (extract v_7012 192 224)) (extract v_7010 224 256)) (extract v_7012 224 256)));
      pure ()
    pat_end
