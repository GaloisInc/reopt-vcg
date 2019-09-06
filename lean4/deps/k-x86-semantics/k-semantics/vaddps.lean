def vaddps1 : instruction :=
  definst "vaddps" $ do
    pattern fun (v_2683 : reg (bv 128)) (v_2684 : reg (bv 128)) (v_2685 : reg (bv 128)) => do
      v_4868 <- getRegister v_2684;
      v_4871 <- getRegister v_2683;
      setRegister (lhs.of_reg v_2685) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4868 0 32) 24 8) (MInt2Float (extract v_4871 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4868 32 64) 24 8) (MInt2Float (extract v_4871 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4868 64 96) 24 8) (MInt2Float (extract v_4871 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4868 96 128) 24 8) (MInt2Float (extract v_4871 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2691 : reg (bv 256)) (v_2692 : reg (bv 256)) (v_2693 : reg (bv 256)) => do
      v_4903 <- getRegister v_2692;
      v_4906 <- getRegister v_2691;
      setRegister (lhs.of_reg v_2693) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4903 0 32) 24 8) (MInt2Float (extract v_4906 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4903 32 64) 24 8) (MInt2Float (extract v_4906 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4903 64 96) 24 8) (MInt2Float (extract v_4906 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4903 96 128) 24 8) (MInt2Float (extract v_4906 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4903 128 160) 24 8) (MInt2Float (extract v_4906 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4903 160 192) 24 8) (MInt2Float (extract v_4906 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4903 192 224) 24 8) (MInt2Float (extract v_4906 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4903 224 256) 24 8) (MInt2Float (extract v_4906 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2675 : Mem) (v_2678 : reg (bv 128)) (v_2679 : reg (bv 128)) => do
      v_9169 <- getRegister v_2678;
      v_9172 <- evaluateAddress v_2675;
      v_9173 <- load v_9172 16;
      setRegister (lhs.of_reg v_2679) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9169 0 32) 24 8) (MInt2Float (extract v_9173 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9169 32 64) 24 8) (MInt2Float (extract v_9173 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9169 64 96) 24 8) (MInt2Float (extract v_9173 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9169 96 128) 24 8) (MInt2Float (extract v_9173 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2686 : Mem) (v_2687 : reg (bv 256)) (v_2688 : reg (bv 256)) => do
      v_9200 <- getRegister v_2687;
      v_9203 <- evaluateAddress v_2686;
      v_9204 <- load v_9203 32;
      setRegister (lhs.of_reg v_2688) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9200 0 32) 24 8) (MInt2Float (extract v_9204 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9200 32 64) 24 8) (MInt2Float (extract v_9204 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9200 64 96) 24 8) (MInt2Float (extract v_9204 64 96) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9200 96 128) 24 8) (MInt2Float (extract v_9204 96 128) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9200 128 160) 24 8) (MInt2Float (extract v_9204 128 160) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9200 160 192) 24 8) (MInt2Float (extract v_9204 160 192) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9200 192 224) 24 8) (MInt2Float (extract v_9204 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9200 224 256) 24 8) (MInt2Float (extract v_9204 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
